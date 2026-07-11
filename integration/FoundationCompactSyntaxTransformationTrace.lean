import integration.FoundationCompactSyntaxTransformationCodeBounds
import integration.FoundationCompactPAAxiomCertificate
import integration.FoundationCompactSyntaxTransformationTraceCore
import integration.FoundationCompactSyntaxNegationTrace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Honest execution traces for compact syntax transformations

This module is the bit-cost layer for the syntax transformations used by the
listed compact verifier.  It also records a binary-coordinate obstruction in
the current unrestricted induction-certificate interface: universal closure
is linear in the *value* of the largest free-variable index, although that
index occupies only logarithmically many certificate bits.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxTransformationTrace

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactSyntaxNegationTrace
open FoundationCompactSyntaxTransformationTraceCore

/-! ## Universal-closure binary length -/

theorem binaryFormulaCode_allClosure_length :
    forall {arity : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity),
      (binaryFormulaCode (∀⁰* formula)).length =
        arity * (binaryNatCode 6).length +
          (binaryFormulaCode formula).length := by
  intro arity
  induction arity with
  | zero =>
      intro formula
      simp
  | succ arity ih =>
      intro formula
      rw [allClosure_succ, ih]
      simp only [binaryFormulaCode, List.length_append]
      simp [Nat.succ_mul, Nat.add_assoc]

theorem binaryFormulaCode_emb_univCl_length_ge_fvSup
    (formula : LO.FirstOrder.ArithmeticProposition) :
    formula.fvSup * (binaryNatCode 6).length <=
      (binaryFormulaCode
        (Rewriting.emb formula.univCl :
          LO.FirstOrder.ArithmeticProposition)).length := by
  rw [Semiformula.coe_univCl_eq_univCl']
  rw [Semiformula.univCl']
  rw [binaryFormulaCode_allClosure_length]
  simpa only [Nat.zero_add] using
    (Nat.le_add_right
      (formula.fvSup * (binaryNatCode 6).length)
      (binaryFormulaCode
        ((Rewriting.app (Rew.fixitr 0 formula.fvSup)) formula)).length)

/-! ## Sparse-index induction certificates -/

def sparseInductionBody (index : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  Semiformula.rel Language.Eq.eq
    ![(&index : LO.FirstOrder.ArithmeticSemiterm Nat 1),
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)]

def sparseInductionCertificate (index : Nat) : PAAxiomCertificate :=
  .induction (sparseInductionBody index)

def sparseInductionCertificateCodeOverhead : Nat :=
  (binaryNatCode 22).length +
    (binaryNatCode 0).length +
    (binaryNatCode 2).length +
    (binaryNatCode
      (Encodable.encode
        (Language.Eq.eq :
          (ℒₒᵣ : LO.FirstOrder.Language).Rel 2))).length +
    (binaryNatCode 1).length +
    (binaryNatCode 0).length +
    (binaryNatCode 0).length + 2

theorem sparseInductionCertificateCode_length_le (index : Nat) :
    (binaryPAAxiomCertificateCode
      (sparseInductionCertificate index)).length <=
        2 * Nat.size index + sparseInductionCertificateCodeOverhead := by
  simp [sparseInductionCertificate, sparseInductionBody,
    binaryPAAxiomCertificateCode, binaryFormulaCode, binaryTermCode,
    sparseInductionCertificateCodeOverhead,
    FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
  omega

theorem sparseInductionCertificateCode_pow_length_le (exponent : Nat) :
    (binaryPAAxiomCertificateCode
      (sparseInductionCertificate (2 ^ exponent))).length <=
        2 * exponent + 2 + sparseInductionCertificateCodeOverhead := by
  have h := sparseInductionCertificateCode_length_le (2 ^ exponent)
  rw [Nat.size_pow] at h
  omega

theorem sparseInduction_succInd_fvSup_ge (index : Nat) :
    index + 1 <= (succInd (sparseInductionBody index)).fvSup := by
  have hfree :
      (succInd (sparseInductionBody index)).FVar? index := by
    simp [sparseInductionBody, succInd, Semiformula.FVar?]
  have hlt := Semiformula.lt_fvSup_of_fvar? hfree
  omega

theorem sparseInductionSentenceCode_length_ge (index : Nat) :
    (index + 1) * (binaryNatCode 6).length <=
      (binaryFormulaCode
        (Rewriting.emb (sparseInductionCertificate index).sentence :
          LO.FirstOrder.ArithmeticProposition)).length := by
  have hclosure := binaryFormulaCode_emb_univCl_length_ge_fvSup
    (succInd (sparseInductionBody index))
  have hfv := sparseInduction_succInd_fvSup_ge index
  have hscaled := Nat.mul_le_mul_right (binaryNatCode 6).length hfv
  exact hscaled.trans (by
    simpa [sparseInductionCertificate, PAAxiomCertificate.sentence,
      Nat.mul_comm] using hclosure)

theorem sparseInductionSentenceCode_pow_length_ge (exponent : Nat) :
    2 ^ exponent <=
      (binaryFormulaCode
        (Rewriting.emb
          (sparseInductionCertificate (2 ^ exponent)).sentence :
            LO.FirstOrder.ArithmeticProposition)).length := by
  have h := sparseInductionSentenceCode_length_ge (2 ^ exponent)
  have htag : 1 <= (binaryNatCode 6).length := by
    have := two_le_binaryNatCode_length 6
    omega
  have hscale :
      2 ^ exponent <=
        (2 ^ exponent + 1) * (binaryNatCode 6).length := by
    calc
      2 ^ exponent <= 2 ^ exponent + 1 := Nat.le_succ _
      _ = (2 ^ exponent + 1) * 1 := by simp
      _ <= (2 ^ exponent + 1) * (binaryNatCode 6).length :=
        Nat.mul_le_mul_left _ htag
  exact hscale.trans h

/-! ## Bound-variable shift -/

def binaryTermBShiftTrace {arity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1) × Nat
  | #index =>
      let input :=
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      let output :=
        (#index.succ :
          LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      (output,
        (binaryTermCode input).length +
          (binaryTermCode output).length + 1)
  | &freeIndex =>
      let input :=
        (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      let output :=
        (&freeIndex :
          LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      (output,
        (binaryTermCode input).length +
          (binaryTermCode output).length + 1)
  | Semiterm.func functionSymbol arguments =>
      let children := fun index =>
        binaryTermBShiftTrace (arguments index)
      (Semiterm.func functionSymbol (fun index => (children index).1),
        1 + Finset.univ.sum (fun index => (children index).2))

theorem binaryTermBShiftTrace_result
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermBShiftTrace term).1 = Rew.bShift term := by
  induction term with
  | bvar index => rfl
  | fvar freeIndex => rfl
  | func functionSymbol arguments ih =>
      simp only [binaryTermBShiftTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermBShiftTrace_cost_pos
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    1 <= (binaryTermBShiftTrace term).2 := by
  cases term <;> simp [binaryTermBShiftTrace]

theorem binaryTermBShiftTrace_cost_le
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermBShiftTrace term).2 <=
      4 * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      let input :=
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have hinput := four_le_binaryTermCode_length input
      have houtput :=
        binaryTermCode_bShift_length_le_add_symbols input
      have hsymbols := termSymbolCount_le_binaryTermCode_length input
      have htraceOutput :
          (binaryTermCode (binaryTermBShiftTrace input).1).length <=
            (binaryTermCode input).length + 2 := by
        rw [binaryTermBShiftTrace_result input]
        simpa [input, termSymbolCount] using houtput
      have hcostEq :
          (binaryTermBShiftTrace input).2 =
            (binaryTermCode input).length +
              (binaryTermCode (binaryTermBShiftTrace input).1).length + 1 := by
        rfl
      dsimp [input] at hinput htraceOutput hcostEq ⊢
      rw [hcostEq]
      omega
  | fvar freeIndex =>
      let input :=
        (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have hinput := four_le_binaryTermCode_length input
      have houtput :=
        binaryTermCode_bShift_length_le_add_symbols input
      have hsymbols := termSymbolCount_le_binaryTermCode_length input
      have htraceOutput :
          (binaryTermCode (binaryTermBShiftTrace input).1).length <=
            (binaryTermCode input).length + 2 := by
        rw [binaryTermBShiftTrace_result input]
        simpa [input, termSymbolCount] using houtput
      have hcostEq :
          (binaryTermBShiftTrace input).2 =
            (binaryTermCode input).length +
              (binaryTermCode (binaryTermBShiftTrace input).1).length + 1 := by
        rfl
      dsimp [input] at hinput htraceOutput hcostEq ⊢
      rw [hcostEq]
      omega
  | func functionSymbol arguments ih =>
      simp only [binaryTermBShiftTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermBShiftTrace (arguments index)).2) <=
            Finset.univ.sum
              (fun index =>
                4 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermBShiftTrace (arguments index)).2) <=
            4 * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  4 * (binaryTermCode (arguments index)).length) :=
            hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader := two_le_binaryNatCode_length 2
      omega

/-! ## The `qpow` image of one bound variable -/

def binarySubstitutionBVarTrace
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (depth : Nat) -> Fin (1 + depth) ->
      LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth) × Nat
  | 0, index =>
      (witness, (binaryTermCode witness).length + 5)
  | depth + 1, index =>
      Fin.cases
        ((#0 : LO.FirstOrder.ArithmeticSemiterm Nat (0 + (depth + 1))),
          2 * depth + 10)
        (fun previousIndex =>
          let previous :=
            binarySubstitutionBVarTrace witness depth previousIndex
          let shifted := binaryTermBShiftTrace previous.1
          (shifted.1,
            previous.2 + shifted.2 + 2 * depth + 10))
        index

theorem binarySubstitutionBVarTrace_result
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth : Nat) (index : Fin (1 + depth)),
      (binarySubstitutionBVarTrace witness depth index).1 =
        ((Rew.subst ![witness]).qpow depth)
          (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      simp [binarySubstitutionBVarTrace, Rew.qpow]
  | succ depth ih =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [binarySubstitutionBVarTrace, Rew.qpow]
      | succ index =>
          simp only [binarySubstitutionBVarTrace, Fin.cases_succ]
          rw [binaryTermBShiftTrace_result, ih]
          simp [Rew.qpow]

def substitutionTraceFactor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat -> Nat
  | 0 => (binaryTermCode witness).length + 5
  | depth + 1 =>
      substitutionTraceFactor witness depth +
        4 * substitutionCodeFactor witness depth + 2 * depth + 10

theorem one_le_substitutionTraceFactor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    1 <= substitutionTraceFactor witness depth := by
  induction depth with
  | zero =>
      simp [substitutionTraceFactor]
  | succ depth ih =>
      simp only [substitutionTraceFactor]
      omega

theorem three_le_substitutionTraceFactor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    3 <= substitutionTraceFactor witness depth := by
  induction depth with
  | zero =>
      have hwitness := four_le_binaryTermCode_length witness
      simp [substitutionTraceFactor]
  | succ depth ih =>
      simp only [substitutionTraceFactor]
      omega

theorem substitutionTraceFactor_monotone
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Monotone (substitutionTraceFactor witness) := by
  apply monotone_nat_of_le_succ
  intro depth
  simp only [substitutionTraceFactor]
  omega

theorem binarySubstitutionBVarTrace_cost_le_factor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth : Nat) (index : Fin (1 + depth)),
      (binarySubstitutionBVarTrace witness depth index).2 <=
        substitutionTraceFactor witness depth := by
  intro depth
  induction depth with
  | zero =>
      intro index
      simp [binarySubstitutionBVarTrace, substitutionTraceFactor]
  | succ depth ih =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp only [binarySubstitutionBVarTrace, Fin.cases_zero,
            substitutionTraceFactor]
          have hfactor := one_le_substitutionTraceFactor witness depth
          omega
      | succ index =>
          simp only [binarySubstitutionBVarTrace, Fin.cases_succ,
            substitutionTraceFactor]
          have hprevious := ih index
          have hshift := binaryTermBShiftTrace_cost_le
            (binarySubstitutionBVarTrace witness depth index).1
          have hresult := binarySubstitutionBVarTrace_result
            witness depth index
          have himage := qpow_substitutionOne_bvar_code_length_le
            witness depth index
          have hcode :
              (binaryTermCode
                (binarySubstitutionBVarTrace witness depth index).1).length <=
                substitutionCodeFactor witness depth := by
            simpa only [hresult] using himage
          have hshift' := hshift.trans
            (Nat.mul_le_mul_left 4 hcode)
          omega

/-! ## Recursive term substitution under `qpow` -/

def binaryTermSubstitutionDirectTrace
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth) ->
      LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth) × Nat
  | #index => binarySubstitutionBVarTrace witness depth index
  | &freeIndex =>
      let input :=
        (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))
      let output :=
        (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth))
      (output,
        (binaryTermCode input).length +
          (binaryTermCode output).length + 1)
  | Semiterm.func functionSymbol arguments =>
      let children := fun index =>
        binaryTermSubstitutionDirectTrace witness depth (arguments index)
      (Semiterm.func functionSymbol (fun index => (children index).1),
        1 + Finset.univ.sum (fun index => (children index).2))

theorem binaryTermSubstitutionDirectTrace_result
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) :
    (binaryTermSubstitutionDirectTrace witness depth term).1 =
      ((Rew.subst ![witness]).qpow depth) term := by
  induction term with
  | bvar index =>
      exact binarySubstitutionBVarTrace_result witness depth index
  | fvar freeIndex =>
      simp [binaryTermSubstitutionDirectTrace,
        qpow_substitutionOne_fvar_eq]
  | func functionSymbol arguments ih =>
      simp only [binaryTermSubstitutionDirectTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermSubstitutionDirectTrace_cost_le_factor_mul
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) :
    (binaryTermSubstitutionDirectTrace witness depth term).2 <=
      substitutionTraceFactor witness depth *
        (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      have hcost := binarySubstitutionBVarTrace_cost_le_factor
        witness depth index
      have hlength := four_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))
      have hfactor := one_le_substitutionTraceFactor witness depth
      have hscale := Nat.mul_le_mul_left
        (substitutionTraceFactor witness depth)
        (show 1 <= (binaryTermCode
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat
              (1 + depth))).length by omega)
      exact hcost.trans (by simpa using hscale)
  | fvar freeIndex =>
      have hfactor := three_le_substitutionTraceFactor witness depth
      have hlength := four_le_binaryTermCode_length
        (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))
      have hscale := Nat.mul_le_mul_right
        (binaryTermCode
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat
            (1 + depth))).length hfactor
      have hbound :
          (binaryTermCode
              (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat
                (1 + depth))).length +
              (binaryTermCode
                (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat
                  (0 + depth))).length + 1 <=
            substitutionTraceFactor witness depth *
              (binaryTermCode
                (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat
                  (1 + depth))).length := by
        simp only [binaryTermCode] at hlength hscale ⊢
        omega
      simpa only [binaryTermSubstitutionDirectTrace] using hbound
  | func functionSymbol arguments ih =>
      rename_i functionArity
      simp only [binaryTermSubstitutionDirectTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn]
      let factor := substitutionTraceFactor witness depth
      let header :=
        (binaryNatCode 2).length +
          (binaryNatCode functionArity).length +
          (binaryNatCode (Encodable.encode functionSymbol)).length
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionDirectTrace witness depth
                  (arguments index)).2) <=
            Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionDirectTrace witness depth
                  (arguments index)).2) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  factor * (binaryTermCode (arguments index)).length) :=
            hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hfactor : 1 <= factor := by
        exact one_le_substitutionTraceFactor witness depth
      have hheader : 1 <= factor * header := by
        have hheaderPos : 1 <= header := by
          dsimp [header]
          have := two_le_binaryNatCode_length 2
          omega
        exact le_trans hheaderPos
          (payload_le_factor_mul_payload
            (factor := factor) (payload := header) hfactor)
      have htotal := Nat.add_le_add hheader hchildren'
      simpa only [factor, header, Nat.mul_add] using htotal

/-! ## Depth-recursive substitution through the generic quantifier lift -/

def binaryTermSubstitutionBaseTrace
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 1 ->
      FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat 0)
  | term@(#_) =>
      (witness, (binaryTermCode term).length +
        (binaryTermCode witness).length + 3)
  | term@(&index) =>
      let result := (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (result, (binaryTermCode term).length +
        (binaryTermCode result).length + 3)
  | Semiterm.func functionSymbol arguments =>
      let traces := fun index =>
        binaryTermSubstitutionBaseTrace witness (arguments index)
      (Semiterm.func functionSymbol (fun index => (traces index).1),
        2 * FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost functionSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))

theorem binaryTermSubstitutionBaseTrace_result
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    (binaryTermSubstitutionBaseTrace witness term).1 =
      (Rew.subst ![witness]) term := by
  induction term with
  | bvar index =>
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      simp [binaryTermSubstitutionBaseTrace]
  | fvar index =>
      simp [binaryTermSubstitutionBaseTrace]
  | func functionSymbol arguments ih =>
      simp only [binaryTermSubstitutionBaseTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermSubstitutionBaseTrace_cost_le
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    (binaryTermSubstitutionBaseTrace witness term).2 <=
      ((binaryTermCode witness).length + 5) *
        (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      have hinput := four_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat 1)
      have hwitness := four_le_binaryTermCode_length witness
      simp only [binaryTermSubstitutionBaseTrace]
      rw [Nat.add_mul]
      nlinarith
  | fvar index =>
      have hinput := four_le_binaryTermCode_length
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1)
      have hfactor :
          3 <= (binaryTermCode witness).length + 5 := by omega
      have hscaled := Nat.mul_le_mul_right
        (binaryTermCode
          (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length
        hfactor
      have hsame :
          (binaryTermCode
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length =
          (binaryTermCode
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length := rfl
      simp only [binaryTermSubstitutionBaseTrace]
      rw [hsame]
      omega
  | func functionSymbol arguments ih =>
      let factor := (binaryTermCode witness).length + 5
      let header :=
        FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost functionSymbol
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionBaseTrace witness
                  (arguments index)).2) <=
            Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionBaseTrace witness
                  (arguments index)).2) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  factor * (binaryTermCode (arguments index)).length) :=
            hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hwitness := four_le_binaryTermCode_length witness
      have hheader : 1 <= header := by
        dsimp [header,
          FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost]
        have htag := two_le_binaryNatCode_length 2
        omega
      have hcharge : 2 * header + 3 <= factor * header := by
        dsimp [factor]
        nlinarith
      simp only [binaryTermSubstitutionBaseTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [factor, header,
        FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost] at hchildren' hcharge ⊢
      omega

theorem binaryTermQTrace_cost_le_general
    {sourceArity targetArity factor codeFactor : Nat}
    (previous : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity ->
      FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat targetArity))
    (hpreviousCost : forall term,
      (previous term).2 <= factor * (binaryTermCode term).length)
    (hpreviousCode : forall term,
      (binaryTermCode (previous term).1).length <=
        codeFactor * (binaryTermCode term).length)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1)) :
    (FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
      previous term).2 <=
      (factor + 20 * codeFactor + 10) *
        (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      cases index using Fin.cases with
      | zero =>
          let input := (#0 : LO.FirstOrder.ArithmeticSemiterm Nat
            (sourceArity + 1))
          have hinput := four_le_binaryTermCode_length input
          have hcostEq :
              (FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace previous input).2 =
                (binaryTermCode input).length +
                (binaryTermCode input).length + 3 := by
            rfl
          rw [hcostEq, Nat.add_mul, Nat.add_mul]
          nlinarith
      | succ index =>
          let old :=
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)
          let current :=
            (#index.succ : LO.FirstOrder.ArithmeticSemiterm Nat
              (sourceArity + 1))
          let rewritten := previous old
          have hinput :
              (binaryTermCode old).length <=
                (binaryTermCode current).length := by
            dsimp [old, current]
            simpa [binaryTermCode] using
              FoundationCompactCanonicalDecodeLength.binaryNatCode_length_mono (Nat.le_succ index.val)
          have hcostOld := hpreviousCost old
          have hcost := hcostOld.trans
            (Nat.mul_le_mul_left factor hinput)
          have hrewritten := hpreviousCode old
          have hrewrittenCurrent :
              (binaryTermCode rewritten.1).length <=
                codeFactor * (binaryTermCode current).length := by
            exact hrewritten.trans
              (Nat.mul_le_mul_left codeFactor hinput)
          have hlift :=
            FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace_cost_le rewritten.1
          have hliftCurrent :
              (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace rewritten.1).2 <=
                16 * (codeFactor *
                  (binaryTermCode current).length) :=
            hlift.trans
              (Nat.mul_le_mul_left 16 hrewrittenCurrent)
          have hliftCodeRaw :=
            binaryTermCode_bShift_length_le_add_symbols rewritten.1
          have hsymbols :=
            termSymbolCount_le_binaryTermCode_length rewritten.1
          have hliftCodeSelf :
              (binaryTermCode
                (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace rewritten.1).1).length <=
                3 * (binaryTermCode rewritten.1).length := by
            rw [FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace_result]
            omega
          have hliftCode :
              (binaryTermCode
                (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace rewritten.1).1).length <=
                3 * (codeFactor *
                  (binaryTermCode current).length) :=
            hliftCodeSelf.trans
              (Nat.mul_le_mul_left 3 hrewrittenCurrent)
          have hcurrent := four_le_binaryTermCode_length current
          simp only [FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace]
          dsimp [old, current, rewritten] at *
          simp only [Nat.add_mul, Nat.mul_assoc]
          omega
  | fvar index =>
      let old :=
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)
      let current :=
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat
          (sourceArity + 1))
      let rewritten := previous old
      have hsame :
          (binaryTermCode old).length =
            (binaryTermCode current).length := by rfl
      have hcostOld := hpreviousCost old
      have hcost :
          rewritten.2 <=
            factor * (binaryTermCode current).length := by
        simpa [rewritten, hsame] using hcostOld
      have hrewritten := hpreviousCode old
      have hrewrittenCurrent :
          (binaryTermCode rewritten.1).length <=
            codeFactor * (binaryTermCode current).length := by
        simpa [rewritten, hsame] using hrewritten
      have hlift :=
        FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace_cost_le rewritten.1
      have hliftCurrent :
          (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace rewritten.1).2 <=
            16 * (codeFactor *
              (binaryTermCode current).length) :=
        hlift.trans (Nat.mul_le_mul_left 16 hrewrittenCurrent)
      have hliftCodeRaw :=
        binaryTermCode_bShift_length_le_add_symbols rewritten.1
      have hsymbols :=
        termSymbolCount_le_binaryTermCode_length rewritten.1
      have hliftCodeSelf :
          (binaryTermCode
            (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace rewritten.1).1).length <=
            3 * (binaryTermCode rewritten.1).length := by
        rw [FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace_result]
        omega
      have hliftCode :
          (binaryTermCode
            (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace rewritten.1).1).length <=
            3 * (codeFactor *
              (binaryTermCode current).length) :=
        hliftCodeSelf.trans
          (Nat.mul_le_mul_left 3 hrewrittenCurrent)
      have hcurrent := four_le_binaryTermCode_length current
      simp only [FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace]
      dsimp [old, current, rewritten] at *
      simp only [Nat.add_mul, Nat.mul_assoc]
      omega
  | func functionSymbol arguments ih =>
      let totalFactor := factor + 20 * codeFactor + 10
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace previous (arguments index)).2) <=
            Finset.univ.sum
              (fun index =>
                totalFactor *
                  (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace previous (arguments index)).2) <=
            totalFactor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  totalFactor *
                    (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost functionSymbol := by
        have htag := two_le_binaryNatCode_length 2
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost]
        omega
      have hcharge :
          2 * FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost functionSymbol + 3 <=
            totalFactor *
              FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost functionSymbol := by
        dsimp [totalFactor]
        nlinarith
      simp only [FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace, binaryTermCode, List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [totalFactor,
        FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost] at hchildren' hcharge ⊢
      omega

def substitutionQpowTraceFactor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat -> Nat
  | 0 => (binaryTermCode witness).length + 5
  | depth + 1 =>
      substitutionQpowTraceFactor witness depth +
        20 * substitutionCodeFactor witness depth + 10

theorem substitutionQpowTraceFactor_monotone
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Monotone (substitutionQpowTraceFactor witness) := by
  apply monotone_nat_of_le_succ
  intro depth
  simp only [substitutionQpowTraceFactor]
  omega

theorem five_le_substitutionQpowTraceFactor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    5 <= substitutionQpowTraceFactor witness depth := by
  have hwitness := four_le_binaryTermCode_length witness
  induction depth with
  | zero => simp [substitutionQpowTraceFactor]
  | succ depth ih =>
      simp only [substitutionQpowTraceFactor]
      omega

def binaryTermSubstitutionQpowTrace
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (depth : Nat) ->
      LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth) ->
        FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
          (LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth))
  | 0 => binaryTermSubstitutionBaseTrace witness
  | depth + 1 =>
      FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
        (binaryTermSubstitutionQpowTrace witness depth)

theorem binaryTermSubstitutionQpowTrace_result
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)),
      (binaryTermSubstitutionQpowTrace witness depth term).1 =
        ((Rew.subst ![witness]).qpow depth) term
  | 0, term => by
      simpa [binaryTermSubstitutionQpowTrace, Rew.qpow] using
        binaryTermSubstitutionBaseTrace_result witness term
  | depth + 1, term => by
      simpa [binaryTermSubstitutionQpowTrace, Rew.qpow] using
        FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace_result
            (binaryTermSubstitutionQpowTrace witness depth)
            ((Rew.subst ![witness]).qpow depth)
            (binaryTermSubstitutionQpowTrace_result witness depth) term

theorem binaryTermSubstitutionQpowTrace_code_length_le
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) :
    (binaryTermCode
      (binaryTermSubstitutionQpowTrace witness depth term).1).length <=
        substitutionCodeFactor witness depth *
          (binaryTermCode term).length := by
  rw [binaryTermSubstitutionQpowTrace_result]
  exact binaryTermCode_substitutionOne_qpow_length_le
    witness depth term

theorem binaryTermSubstitutionQpowTrace_cost_le_factor_mul
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)),
      (binaryTermSubstitutionQpowTrace witness depth term).2 <=
        substitutionQpowTraceFactor witness depth *
          (binaryTermCode term).length
  | 0, term => by
      simpa [binaryTermSubstitutionQpowTrace,
        substitutionQpowTraceFactor] using
          binaryTermSubstitutionBaseTrace_cost_le witness term
  | depth + 1, term => by
      have h := binaryTermQTrace_cost_le_general
        (binaryTermSubstitutionQpowTrace witness depth)
        (binaryTermSubstitutionQpowTrace_cost_le_factor_mul
          witness depth)
        (binaryTermSubstitutionQpowTrace_code_length_le
          witness depth) term
      simpa only [binaryTermSubstitutionQpowTrace,
        substitutionQpowTraceFactor] using h

theorem substitutionQpowTraceFactor_le_polynomial
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall depth : Nat,
      substitutionQpowTraceFactor witness depth <=
        32 * (depth + 1) ^ 2 *
          ((binaryTermCode witness).length + 1) := by
  intro depth
  induction depth with
  | zero =>
      have hwitness := four_le_binaryTermCode_length witness
      simp [substitutionQpowTraceFactor]
      nlinarith
  | succ depth ih =>
      have hsymbols := termSymbolCount_le_binaryTermCode_length witness
      have hwitness := four_le_binaryTermCode_length witness
      simp only [substitutionQpowTraceFactor]
      rw [substitutionCodeFactor_eq]
      nlinarith

/-! ## Formula substitution through the generic rewriting trace -/

/-- Formula-level one-variable substitution at an arbitrary quantifier depth.
The formula traversal is exactly the generic recursive rewriting trace; its
term callback is the depth-indexed substitution trace above. -/
def binaryFormulaSubstitutionQpowTrace
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (1 + depth)) :
    FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
      (LO.FirstOrder.ArithmeticSemiformula Nat (0 + depth)) :=
  FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace
    (binaryTermSubstitutionQpowTrace witness depth) formula

theorem binaryFormulaSubstitutionQpowTrace_result
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (1 + depth)) :
    (binaryFormulaSubstitutionQpowTrace witness depth formula).1 =
      Rewriting.app ((Rew.subst ![witness]).qpow depth) formula := by
  simpa only [binaryFormulaSubstitutionQpowTrace] using
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace_result
        (binaryTermSubstitutionQpowTrace witness depth)
        ((Rew.subst ![witness]).qpow depth)
        (binaryTermSubstitutionQpowTrace_result witness depth)
        formula

theorem binaryFormulaSubstitutionHeaderCharge_le
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (budget header : Nat)
    (hheader : 1 <= header) :
    2 * header + 3 <=
      substitutionQpowTraceFactor witness budget * header := by
  have hfactor := five_le_substitutionQpowTraceFactor witness budget
  have hscaled := Nat.mul_le_mul_right header hfactor
  omega

theorem binaryFormulaSubstitutionQpowTrace_cost_le
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth : Nat)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat (1 + depth))
      (budget : Nat),
      depth + formulaSymbolCount formula <= budget ->
      (binaryFormulaSubstitutionQpowTrace witness depth formula).2 <=
        substitutionQpowTraceFactor witness budget *
          (binaryFormulaCode formula).length
  | depth, ⊤, budget, hbudget => by
      change
        2 * FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 2 + 3 <=
          substitutionQpowTraceFactor witness budget *
            FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 2
      apply binaryFormulaSubstitutionHeaderCharge_le
      have htag := two_le_binaryNatCode_length 2
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
      omega
  | depth, ⊥, budget, hbudget => by
      change
        2 * FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 3 + 3 <=
          substitutionQpowTraceFactor witness budget *
            FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 3
      apply binaryFormulaSubstitutionHeaderCharge_le
      have htag := two_le_binaryNatCode_length 3
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
      omega
  | depth, Semiformula.rel relationSymbol arguments, budget, hbudget => by
      let factor := substitutionQpowTraceFactor witness budget
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.rel relationSymbol arguments)
        omega
      have hmono := substitutionQpowTraceFactor_monotone witness hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionQpowTrace witness depth
                  (arguments index)).2) <=
            Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        have hterm :=
          binaryTermSubstitutionQpowTrace_cost_le_factor_mul
            witness depth (arguments index)
        exact hterm.trans
          (Nat.mul_le_mul_right
            (binaryTermCode (arguments index)).length hmono)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionQpowTrace witness depth
                  (arguments index)).2) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) :=
            hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 0 relationSymbol := by
        have htag := two_le_binaryNatCode_length 0
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaSubstitutionHeaderCharge_le
        witness budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 0 relationSymbol) hheader
      simp only [binaryFormulaSubstitutionQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [factor,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost] at hchildren' hcharge ⊢
      omega
  | depth, Semiformula.nrel relationSymbol arguments, budget, hbudget => by
      let factor := substitutionQpowTraceFactor witness budget
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.nrel relationSymbol arguments)
        omega
      have hmono := substitutionQpowTraceFactor_monotone witness hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionQpowTrace witness depth
                  (arguments index)).2) <=
            Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        have hterm :=
          binaryTermSubstitutionQpowTrace_cost_le_factor_mul
            witness depth (arguments index)
        exact hterm.trans
          (Nat.mul_le_mul_right
            (binaryTermCode (arguments index)).length hmono)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermSubstitutionQpowTrace witness depth
                  (arguments index)).2) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) :=
            hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 1 relationSymbol := by
        have htag := two_le_binaryNatCode_length 1
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaSubstitutionHeaderCharge_le
        witness budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 1 relationSymbol) hheader
      simp only [binaryFormulaSubstitutionQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [factor,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost] at hchildren' hcharge ⊢
      omega
  | depth, left ⋏ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaSubstitutionQpowTrace_cost_le
        witness depth left budget hleftBudget
      have hright := binaryFormulaSubstitutionQpowTrace_cost_le
        witness depth right budget hrightBudget
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 4 := by
        have htag := two_le_binaryNatCode_length 4
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaSubstitutionHeaderCharge_le
        witness budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 4) hheader
      unfold binaryFormulaSubstitutionQpowTrace at hleft hright
      simp only [binaryFormulaSubstitutionQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega
  | depth, left ⋎ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaSubstitutionQpowTrace_cost_le
        witness depth left budget hleftBudget
      have hright := binaryFormulaSubstitutionQpowTrace_cost_le
        witness depth right budget hrightBudget
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5 := by
        have htag := two_le_binaryNatCode_length 5
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaSubstitutionHeaderCharge_le
        witness budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5) hheader
      unfold binaryFormulaSubstitutionQpowTrace at hleft hright
      simp only [binaryFormulaSubstitutionQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega
  | depth, ∀⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaSubstitutionQpowTrace_cost_le
        witness (depth + 1) body budget hbodyBudget
      have hq :
          FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
              (binaryTermSubstitutionQpowTrace witness depth) =
            binaryTermSubstitutionQpowTrace witness (depth + 1) := by
        funext term
        rfl
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6 := by
        have htag := two_le_binaryNatCode_length 6
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaSubstitutionHeaderCharge_le
        witness budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6) hheader
      unfold binaryFormulaSubstitutionQpowTrace at hbody ⊢
      simp only [
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace]
      rw [hq]
      simp only [binaryFormulaCode, List.length_append]
      rw [Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega
  | depth, ∃⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaSubstitutionQpowTrace_cost_le
        witness (depth + 1) body budget hbodyBudget
      have hq :
          FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
              (binaryTermSubstitutionQpowTrace witness depth) =
            binaryTermSubstitutionQpowTrace witness (depth + 1) := by
        funext term
        rfl
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 7 := by
        have htag := two_le_binaryNatCode_length 7
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaSubstitutionHeaderCharge_le
        witness budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 7) hheader
      unfold binaryFormulaSubstitutionQpowTrace at hbody ⊢
      simp only [
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace]
      rw [hq]
      simp only [binaryFormulaCode, List.length_append]
      rw [Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega
/-! ## Eliminate the internal depth budget -/

theorem substitutionTraceFactor_le_polynomial
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall depth : Nat,
      substitutionTraceFactor witness depth <=
        16 * (depth + 1) ^ 2 *
          ((binaryTermCode witness).length + 1) := by
  intro depth
  induction depth with
  | zero =>
      have hbase :
          (binaryTermCode witness).length + 5 <=
            16 * ((binaryTermCode witness).length + 1) := by
        omega
      simpa [substitutionTraceFactor] using hbase
  | succ depth ih =>
      have hsymbols := termSymbolCount_le_binaryTermCode_length witness
      have hwitness := four_le_binaryTermCode_length witness
      simp only [substitutionTraceFactor]
      rw [substitutionCodeFactor_eq]
      nlinarith [ih, hsymbols]

def binaryFormulaSubstitutionOneTrace
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition × Nat :=
  binaryFormulaSubstitutionQpowTrace witness 0 formula

theorem binaryFormulaSubstitutionOneTrace_result
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFormulaSubstitutionOneTrace formula witness).1 =
      formula/[witness] := by
  simpa [binaryFormulaSubstitutionOneTrace, Rew.qpow] using
    binaryFormulaSubstitutionQpowTrace_result witness 0 formula

theorem binaryFormulaSubstitutionOneTrace_cost_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFormulaSubstitutionOneTrace formula witness).2 <=
      32 * ((binaryFormulaCode formula).length + 1) ^ 2 *
        ((binaryTermCode witness).length + 1) *
        (binaryFormulaCode formula).length := by
  let formulaLength := (binaryFormulaCode formula).length
  let witnessLength := (binaryTermCode witness).length
  have hbudget :
      0 + formulaSymbolCount formula <= formulaSymbolCount formula := by
    simp
  have htrace := binaryFormulaSubstitutionQpowTrace_cost_le
    witness 0 formula (formulaSymbolCount formula) hbudget
  have hfactor := substitutionQpowTraceFactor_le_polynomial
    witness (formulaSymbolCount formula)
  have hsymbols := formulaSymbolCount_le_binaryFormulaCode_length formula
  have hpow :
      (formulaSymbolCount formula + 1) ^ 2 <=
        ((binaryFormulaCode formula).length + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hsymbols 1) 2
  have hfactor' :
      substitutionQpowTraceFactor witness (formulaSymbolCount formula) <=
        32 * ((binaryFormulaCode formula).length + 1) ^ 2 *
          ((binaryTermCode witness).length + 1) := by
    exact hfactor.trans
      (Nat.mul_le_mul_right ((binaryTermCode witness).length + 1)
        (Nat.mul_le_mul_left 32 hpow))
  have hscaled := Nat.mul_le_mul_right
    (binaryFormulaCode formula).length hfactor'
  exact htrace.trans (by
    simpa [binaryFormulaSubstitutionOneTrace,
      Nat.mul_assoc] using hscaled)

/-! ## Honest one-pass `fixitr` below quantifiers -/

/-- Lift the one-pass base `fixitr` trace through exactly `depth` quantifier
layers.  The successor clause executes `Rew.q` through the charged core
`binaryTermQTrace`; it does not replace that work by an extensional rewrite. -/
def binaryTermFixitrQpowTrace (m : Nat) :
    (depth : Nat) ->
      LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth) ->
        FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
          (LO.FirstOrder.ArithmeticSemiterm Nat ((0 + m) + depth))
  | 0 =>
      FoundationCompactSyntaxTransformationTraceCore.binaryTermFixitrTrace m
  | depth + 1 =>
      FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
        (binaryTermFixitrQpowTrace m depth)

theorem binaryTermFixitrQpowTrace_result (m : Nat) :
    forall (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth)),
      (binaryTermFixitrQpowTrace m depth term).1 =
        ((Rew.fixitr (L := ℒₒᵣ) 0 m).qpow depth) term
  | 0, term => by
      simpa [binaryTermFixitrQpowTrace, Rew.qpow] using
        FoundationCompactSyntaxTransformationTraceCore.binaryTermFixitrTrace_result m term
  | depth + 1, term => by
      simpa [binaryTermFixitrQpowTrace, Rew.qpow] using
        FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace_result
            (binaryTermFixitrQpowTrace m depth)
            ((Rew.fixitr (L := ℒₒᵣ) 0 m).qpow depth)
            (binaryTermFixitrQpowTrace_result m depth) term

theorem fixitrTermImageBound_one (m : Nat) :
    RewritingTermImageBound
      (Rew.fixitr (L := ℒₒᵣ) 0 m) 1 := by
  constructor
  · intro index
    exact Fin.elim0 index
  · intro index
    rw [Rew.fixitr_fvar]
    split <;> simp [termSymbolCount]

theorem fixitrQpowTermImageBound_one (m : Nat) :
    forall depth : Nat,
      RewritingTermImageBound
        ((Rew.fixitr (L := ℒₒᵣ) 0 m).qpow depth) 1
  | 0 => by
      simpa [Rew.qpow] using fixitrTermImageBound_one m
  | depth + 1 => by
      simpa [Rew.qpow] using
        (fixitrQpowTermImageBound_one m depth).q (by omega)

theorem binaryTermFixitrQpowTrace_symbol_count_le
    (m depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth)) :
    termSymbolCount (binaryTermFixitrQpowTrace m depth term).1 <=
      termSymbolCount term := by
  rw [binaryTermFixitrQpowTrace_result]
  simpa using termSymbolCount_rewriting_le_mul
    ((Rew.fixitr (L := ℒₒᵣ) 0 m).qpow depth)
    (by omega) (fixitrQpowTermImageBound_one m depth) term

/-- One charged `q` layer increases a multiplicative output-code factor by
at most two when the previous trace does not increase symbol count. -/
theorem binaryTermQTrace_code_length_le_general
    {sourceArity targetArity codeFactor : Nat}
    (previous : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity ->
      FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat targetArity))
    (hone : 1 <= codeFactor)
    (hpreviousCode : forall term,
      (binaryTermCode (previous term).1).length <=
        codeFactor * (binaryTermCode term).length)
    (hpreviousSymbols : forall term,
      termSymbolCount (previous term).1 <= termSymbolCount term)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1)) :
    (binaryTermCode
      (FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
        previous term).1).length <=
      (codeFactor + 2) * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      cases index using Fin.cases with
      | zero =>
          have hfactor : 1 <= codeFactor + 2 := by omega
          simp only [FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace,
            Fin.cases_zero]
          change
            (binaryNatCode 0 ++ binaryNatCode 0).length <=
              (codeFactor + 2) *
                (binaryNatCode 0 ++ binaryNatCode 0).length
          exact payload_le_factor_mul_payload hfactor
      | succ index =>
          have hinput :
              (binaryTermCode
                (#index : LO.FirstOrder.ArithmeticSemiterm Nat
                  sourceArity)).length <=
                (binaryTermCode
                  (#index.succ : LO.FirstOrder.ArithmeticSemiterm Nat
                    (sourceArity + 1))).length := by
            simpa [binaryTermCode] using
              FoundationCompactCanonicalDecodeLength.binaryNatCode_length_mono (Nat.le_succ index.val)
          have hcode := hpreviousCode
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)
          have hcode' := hcode.trans
            (Nat.mul_le_mul_left codeFactor hinput)
          have hsymbols := hpreviousSymbols
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)
          have hshift := binaryTermCode_bShift_length_le_add_symbols
            (previous
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)).1
          have hcurrent := four_le_binaryTermCode_length
            (#index.succ : LO.FirstOrder.ArithmeticSemiterm Nat
              (sourceArity + 1))
          simp only [FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace]
          simp only [Fin.cases_succ]
          change
            (binaryTermCode
              (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace
                  (previous
                    (#index : LO.FirstOrder.ArithmeticSemiterm Nat
                      sourceArity)).1).1).length <=
              (codeFactor + 2) *
                (binaryTermCode
                  (#index.succ : LO.FirstOrder.ArithmeticSemiterm Nat
                    (sourceArity + 1))).length
          rw [FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace_result]
          rw [Nat.add_mul]
          simp only [termSymbolCount] at hsymbols
          omega
  | fvar index =>
      have hcode := hpreviousCode
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)
      have hsame :
          (binaryTermCode
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)).length =
          (binaryTermCode
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat
              (sourceArity + 1))).length := rfl
      have hcode' :
          (binaryTermCode
            (previous
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                sourceArity)).1).length <=
            codeFactor *
              (binaryTermCode
                (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                  (sourceArity + 1))).length := by
        rw [← hsame]
        exact hcode
      have hsymbols := hpreviousSymbols
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)
      have hshift := binaryTermCode_bShift_length_le_add_symbols
        (previous
          (&index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)).1
      have hcurrent := four_le_binaryTermCode_length
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat
          (sourceArity + 1))
      simp only [FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace]
      change
        (binaryTermCode
          (FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace
              (previous
                (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                  sourceArity)).1).1).length <=
          (codeFactor + 2) *
            (binaryTermCode
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                (sourceArity + 1))).length
      rw [FoundationCompactSyntaxTransformationTraceCore.binaryTermBShiftTrace_result]
      rw [Nat.add_mul]
      simp only [termSymbolCount] at hsymbols
      omega
  | func functionSymbol arguments ih =>
      let factor := codeFactor + 2
      let header :=
        FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost functionSymbol
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  (FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace previous (arguments index)).1).length) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) :=
            Finset.sum_le_sum (fun index _ => ih index)
          _ = _ := by rw [Finset.mul_sum]
      have hfactor : 1 <= factor := by dsimp [factor]; omega
      have hheader : header <= factor * header := by
        have := Nat.mul_le_mul_left header hfactor
        simpa [Nat.mul_comm] using this
      simp only [FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace, binaryTermCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn, Nat.mul_add]
      dsimp [factor, header,
        FoundationCompactSyntaxTransformationTraceCore.binaryTermFunctionHeaderCost] at hchildren hheader ⊢
      omega

def fixitrQpowCodeFactor : Nat -> Nat
  | 0 => 1
  | depth + 1 => fixitrQpowCodeFactor depth + 2

theorem fixitrQpowCodeFactor_eq (depth : Nat) :
    fixitrQpowCodeFactor depth = 2 * depth + 1 := by
  induction depth with
  | zero => simp [fixitrQpowCodeFactor]
  | succ depth ih =>
      simp only [fixitrQpowCodeFactor, ih]
      omega

theorem one_le_fixitrQpowCodeFactor (depth : Nat) :
    1 <= fixitrQpowCodeFactor depth := by
  rw [fixitrQpowCodeFactor_eq]
  omega

theorem fixitrQpowCodeFactor_monotone :
    Monotone fixitrQpowCodeFactor := by
  intro left right h
  rw [fixitrQpowCodeFactor_eq, fixitrQpowCodeFactor_eq]
  omega

theorem binaryTermFixitrQpowTrace_code_length_le (m : Nat) :
    forall (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth)),
      (binaryTermCode (binaryTermFixitrQpowTrace m depth term).1).length <=
        fixitrQpowCodeFactor depth * (binaryTermCode term).length
  | 0, term => by
      simpa [binaryTermFixitrQpowTrace, fixitrQpowCodeFactor] using
        FoundationCompactSyntaxTransformationTraceCore.binaryTermFixitrTrace_code_length_le m term
  | depth + 1, term => by
      have h := binaryTermQTrace_code_length_le_general
        (binaryTermFixitrQpowTrace m depth)
        (one_le_fixitrQpowCodeFactor depth)
        (binaryTermFixitrQpowTrace_code_length_le m depth)
        (binaryTermFixitrQpowTrace_symbol_count_le m depth) term
      simpa only [binaryTermFixitrQpowTrace,
        fixitrQpowCodeFactor] using h

def fixitrQpowTraceFactor (m : Nat) : Nat -> Nat
  | 0 => 32 * (m + 1)
  | depth + 1 =>
      fixitrQpowTraceFactor m depth +
        20 * fixitrQpowCodeFactor depth + 10

theorem fixitrQpowTraceFactor_monotone (m : Nat) :
    Monotone (fixitrQpowTraceFactor m) := by
  apply monotone_nat_of_le_succ
  intro depth
  simp only [fixitrQpowTraceFactor]
  omega

theorem five_le_fixitrQpowTraceFactor (m depth : Nat) :
    5 <= fixitrQpowTraceFactor m depth := by
  induction depth with
  | zero =>
      simp only [fixitrQpowTraceFactor]
      omega
  | succ depth ih =>
      simp only [fixitrQpowTraceFactor]
      omega

theorem binaryTermFixitrQpowTrace_cost_le_factor_mul (m : Nat) :
    forall (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth)),
      (binaryTermFixitrQpowTrace m depth term).2 <=
        fixitrQpowTraceFactor m depth * (binaryTermCode term).length
  | 0, term => by
      simpa [binaryTermFixitrQpowTrace,
        fixitrQpowTraceFactor] using
          FoundationCompactSyntaxTransformationTraceCore.binaryTermFixitrTrace_cost_le m term
  | depth + 1, term => by
      have h := binaryTermQTrace_cost_le_general
        (binaryTermFixitrQpowTrace m depth)
        (binaryTermFixitrQpowTrace_cost_le_factor_mul m depth)
        (binaryTermFixitrQpowTrace_code_length_le m depth) term
      simpa only [binaryTermFixitrQpowTrace,
        fixitrQpowTraceFactor] using h

theorem fixitrQpowTraceFactor_le_polynomial (m : Nat) :
    forall depth : Nat,
      fixitrQpowTraceFactor m depth <=
        128 * (m + depth + 1) ^ 2 := by
  intro depth
  induction depth with
  | zero =>
      simp [fixitrQpowTraceFactor]
      nlinarith
  | succ depth ih =>
      simp only [fixitrQpowTraceFactor, fixitrQpowCodeFactor_eq]
      calc
        fixitrQpowTraceFactor m depth +
              20 * (2 * depth + 1) + 10 <=
            128 * (m + depth + 1) ^ 2 +
              20 * (2 * depth + 1) + 10 := by omega
        _ <= 128 * (m + (depth + 1) + 1) ^ 2 := by
          have hdepth : depth + 1 <= m + depth + 1 := by omega
          simp only [pow_two]
          nlinarith

/-- Formula traversal driven by the depth-indexed term trace above. -/
def binaryFormulaFixitrQpowTrace
    (m depth : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (0 + depth)) :
    FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
      (LO.FirstOrder.ArithmeticSemiformula Nat ((0 + m) + depth)) :=
  FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace
    (binaryTermFixitrQpowTrace m depth) formula

theorem binaryFormulaFixitrQpowTrace_result
    (m depth : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (0 + depth)) :
    (binaryFormulaFixitrQpowTrace m depth formula).1 =
      Rewriting.app ((Rew.fixitr (L := ℒₒᵣ) 0 m).qpow depth)
        formula := by
  simpa only [binaryFormulaFixitrQpowTrace] using
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace_result
        (binaryTermFixitrQpowTrace m depth)
        ((Rew.fixitr (L := ℒₒᵣ) 0 m).qpow depth)
        (binaryTermFixitrQpowTrace_result m depth) formula

theorem binaryFormulaFixitrQpowTrace_code_length_le (m : Nat) :
    forall (depth : Nat)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat (0 + depth))
      (budget : Nat),
      depth + formulaSymbolCount formula <= budget ->
      (binaryFormulaCode
        (binaryFormulaFixitrQpowTrace m depth formula).1).length <=
        fixitrQpowCodeFactor budget *
          (binaryFormulaCode formula).length
  | depth, ⊤, budget, hbudget => by
      have hfactor := one_le_fixitrQpowCodeFactor budget
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace]
      exact payload_le_factor_mul_payload hfactor
  | depth, ⊥, budget, hbudget => by
      have hfactor := one_le_fixitrQpowCodeFactor budget
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace]
      exact payload_le_factor_mul_payload hfactor
  | depth, Semiformula.rel relationSymbol arguments, budget, hbudget => by
      let factor := fixitrQpowCodeFactor budget
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.rel relationSymbol arguments)
        omega
      have hmono := fixitrQpowCodeFactor_monotone hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  (binaryTermFixitrQpowTrace m depth
                    (arguments index)).1).length) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
            apply Finset.sum_le_sum
            intro index hindex
            exact (binaryTermFixitrQpowTrace_code_length_le
              m depth (arguments index)).trans
                (Nat.mul_le_mul_right
                  (binaryTermCode (arguments index)).length hmono)
          _ = _ := by rw [Finset.mul_sum]
      have hfactor : 1 <= factor := by
        dsimp [factor]
        exact one_le_fixitrQpowCodeFactor budget
      have hheader := payload_le_factor_mul_payload
        (factor := factor)
        (payload := FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 0 relationSymbol) hfactor
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn, Nat.mul_add]
      dsimp [factor,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost] at hchildren hheader ⊢
      omega
  | depth, Semiformula.nrel relationSymbol arguments, budget, hbudget => by
      let factor := fixitrQpowCodeFactor budget
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.nrel relationSymbol arguments)
        omega
      have hmono := fixitrQpowCodeFactor_monotone hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  (binaryTermFixitrQpowTrace m depth
                    (arguments index)).1).length) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
            apply Finset.sum_le_sum
            intro index hindex
            exact (binaryTermFixitrQpowTrace_code_length_le
              m depth (arguments index)).trans
                (Nat.mul_le_mul_right
                  (binaryTermCode (arguments index)).length hmono)
          _ = _ := by rw [Finset.mul_sum]
      have hfactor : 1 <= factor := by
        dsimp [factor]
        exact one_le_fixitrQpowCodeFactor budget
      have hheader := payload_le_factor_mul_payload
        (factor := factor)
        (payload := FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 1 relationSymbol) hfactor
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn, Nat.mul_add]
      dsimp [factor,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost] at hchildren hheader ⊢
      omega
  | depth, left ⋏ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaFixitrQpowTrace_code_length_le
        m depth left budget hleftBudget
      have hright := binaryFormulaFixitrQpowTrace_code_length_le
        m depth right budget hrightBudget
      unfold binaryFormulaFixitrQpowTrace at hleft hright
      have hfactor := one_le_fixitrQpowCodeFactor budget
      have hheader := payload_le_factor_mul_payload
        (factor := fixitrQpowCodeFactor budget)
        (payload := FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 4) hfactor
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hheader ⊢
      omega
  | depth, left ⋎ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaFixitrQpowTrace_code_length_le
        m depth left budget hleftBudget
      have hright := binaryFormulaFixitrQpowTrace_code_length_le
        m depth right budget hrightBudget
      unfold binaryFormulaFixitrQpowTrace at hleft hright
      have hfactor := one_le_fixitrQpowCodeFactor budget
      have hheader := payload_le_factor_mul_payload
        (factor := fixitrQpowCodeFactor budget)
        (payload := FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5) hfactor
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hheader ⊢
      omega
  | depth, ∀⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaFixitrQpowTrace_code_length_le
        m (depth + 1) body budget hbodyBudget
      unfold binaryFormulaFixitrQpowTrace at hbody
      have hq :
          FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
              (binaryTermFixitrQpowTrace m depth) =
            binaryTermFixitrQpowTrace m (depth + 1) := by
        funext term
        rfl
      have hfactor := one_le_fixitrQpowCodeFactor budget
      have hheader := payload_le_factor_mul_payload
        (factor := fixitrQpowCodeFactor budget)
        (payload := FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6) hfactor
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [hq, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hheader ⊢
      omega
  | depth, ∃⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaFixitrQpowTrace_code_length_le
        m (depth + 1) body budget hbodyBudget
      unfold binaryFormulaFixitrQpowTrace at hbody
      have hq :
          FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
              (binaryTermFixitrQpowTrace m depth) =
            binaryTermFixitrQpowTrace m (depth + 1) := by
        funext term
        rfl
      have hfactor := one_le_fixitrQpowCodeFactor budget
      have hheader := payload_le_factor_mul_payload
        (factor := fixitrQpowCodeFactor budget)
        (payload := FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 7) hfactor
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [hq, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hheader ⊢
      omega

theorem binaryFormulaFixitrHeaderCharge_le
    (m budget header : Nat) (hheader : 1 <= header) :
    2 * header + 3 <=
      fixitrQpowTraceFactor m budget * header := by
  have hfactor := five_le_fixitrQpowTraceFactor m budget
  have hscaled := Nat.mul_le_mul_right header hfactor
  omega

theorem binaryFormulaFixitrQpowTrace_cost_le (m : Nat) :
    forall (depth : Nat)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat (0 + depth))
      (budget : Nat),
      depth + formulaSymbolCount formula <= budget ->
      (binaryFormulaFixitrQpowTrace m depth formula).2 <=
        fixitrQpowTraceFactor m budget *
          (binaryFormulaCode formula).length
  | depth, ⊤, budget, hbudget => by
      change
        2 * FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 2 + 3 <=
          fixitrQpowTraceFactor m budget *
            FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 2
      apply binaryFormulaFixitrHeaderCharge_le
      have htag := two_le_binaryNatCode_length 2
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
      omega
  | depth, ⊥, budget, hbudget => by
      change
        2 * FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 3 + 3 <=
          fixitrQpowTraceFactor m budget *
            FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 3
      apply binaryFormulaFixitrHeaderCharge_le
      have htag := two_le_binaryNatCode_length 3
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
      omega
  | depth, Semiformula.rel relationSymbol arguments, budget, hbudget => by
      let factor := fixitrQpowTraceFactor m budget
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.rel relationSymbol arguments)
        omega
      have hmono := fixitrQpowTraceFactor_monotone m hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFixitrQpowTrace m depth
                  (arguments index)).2) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
            apply Finset.sum_le_sum
            intro index hindex
            exact (binaryTermFixitrQpowTrace_cost_le_factor_mul
              m depth (arguments index)).trans
                (Nat.mul_le_mul_right
                  (binaryTermCode (arguments index)).length hmono)
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 0 relationSymbol := by
        have htag := two_le_binaryNatCode_length 0
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaFixitrHeaderCharge_le
        m budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 0 relationSymbol) hheader
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [factor,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost] at hchildren hcharge ⊢
      omega
  | depth, Semiformula.nrel relationSymbol arguments, budget, hbudget => by
      let factor := fixitrQpowTraceFactor m budget
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.nrel relationSymbol arguments)
        omega
      have hmono := fixitrQpowTraceFactor_monotone m hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFixitrQpowTrace m depth
                  (arguments index)).2) <=
            factor * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
            apply Finset.sum_le_sum
            intro index hindex
            exact (binaryTermFixitrQpowTrace_cost_le_factor_mul
              m depth (arguments index)).trans
                (Nat.mul_le_mul_right
                  (binaryTermCode (arguments index)).length hmono)
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 1 relationSymbol := by
        have htag := two_le_binaryNatCode_length 1
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaFixitrHeaderCharge_le
        m budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost 1 relationSymbol) hheader
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [factor,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaAtomHeaderCost] at hchildren hcharge ⊢
      omega
  | depth, left ⋏ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaFixitrQpowTrace_cost_le
        m depth left budget hleftBudget
      have hright := binaryFormulaFixitrQpowTrace_cost_le
        m depth right budget hrightBudget
      unfold binaryFormulaFixitrQpowTrace at hleft hright
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 4 := by
        have htag := two_le_binaryNatCode_length 4
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaFixitrHeaderCharge_le
        m budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 4) hheader
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega
  | depth, left ⋎ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaFixitrQpowTrace_cost_le
        m depth left budget hleftBudget
      have hright := binaryFormulaFixitrQpowTrace_cost_le
        m depth right budget hrightBudget
      unfold binaryFormulaFixitrQpowTrace at hleft hright
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5 := by
        have htag := two_le_binaryNatCode_length 5
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaFixitrHeaderCharge_le
        m budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5) hheader
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega
  | depth, ∀⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaFixitrQpowTrace_cost_le
        m (depth + 1) body budget hbodyBudget
      unfold binaryFormulaFixitrQpowTrace at hbody
      have hq :
          FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
              (binaryTermFixitrQpowTrace m depth) =
            binaryTermFixitrQpowTrace m (depth + 1) := by
        funext term
        rfl
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6 := by
        have htag := two_le_binaryNatCode_length 6
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaFixitrHeaderCharge_le
        m budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6) hheader
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [hq, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega
  | depth, ∃⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaFixitrQpowTrace_cost_le
        m (depth + 1) body budget hbodyBudget
      unfold binaryFormulaFixitrQpowTrace at hbody
      have hq :
          FoundationCompactSyntaxTransformationTraceCore.binaryTermQTrace
              (binaryTermFixitrQpowTrace m depth) =
            binaryTermFixitrQpowTrace m (depth + 1) := by
        funext term
        rfl
      have hheader :
          1 <= FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 7 := by
        have htag := two_le_binaryNatCode_length 7
        dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaFixitrHeaderCharge_le
        m budget
        (FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 7) hheader
      simp only [binaryFormulaFixitrQpowTrace,
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [hq, Nat.mul_add]
      dsimp [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost] at hcharge ⊢
      omega

def binaryFormulaFixitrTrace
    (m : Nat) (formula : LO.FirstOrder.ArithmeticProposition) :
    FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
      (LO.FirstOrder.ArithmeticSemiformula Nat (0 + m)) :=
  binaryFormulaFixitrQpowTrace m 0 formula

theorem binaryFormulaFixitrTrace_result
    (m : Nat) (formula : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaFixitrTrace m formula).1 =
      Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 m) formula := by
  simpa [binaryFormulaFixitrTrace, Rew.qpow] using
    binaryFormulaFixitrQpowTrace_result m 0 formula

theorem binaryFormulaFixitrTrace_code_length_le
    (m : Nat) (formula : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode (binaryFormulaFixitrTrace m formula).1).length <=
      4 * ((binaryFormulaCode formula).length + 1) ^ 2 := by
  let symbolCount := formulaSymbolCount formula
  let codeLength := (binaryFormulaCode formula).length
  have hbudget : 0 + symbolCount <= symbolCount := by simp
  have htrace := binaryFormulaFixitrQpowTrace_code_length_le
    m 0 formula symbolCount hbudget
  have hsymbols : symbolCount <= codeLength := by
    exact formulaSymbolCount_le_binaryFormulaCode_length formula
  have hfactor :
      fixitrQpowCodeFactor symbolCount <= 3 * (codeLength + 1) := by
    rw [fixitrQpowCodeFactor_eq]
    omega
  have hscaled := Nat.mul_le_mul_right codeLength hfactor
  have hbound :
      fixitrQpowCodeFactor symbolCount * codeLength <=
        4 * (codeLength + 1) ^ 2 := by
    nlinarith
  exact htrace.trans (by
    simpa [binaryFormulaFixitrTrace, symbolCount, codeLength] using hbound)

theorem binaryFormulaFixitrTrace_cost_le
    (m : Nat) (formula : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaFixitrTrace m formula).2 <=
      128 *
        (m + (binaryFormulaCode formula).length + 1) ^ 2 *
          (binaryFormulaCode formula).length := by
  let symbolCount := formulaSymbolCount formula
  let codeLength := (binaryFormulaCode formula).length
  have hbudget : 0 + symbolCount <= symbolCount := by simp
  have htrace := binaryFormulaFixitrQpowTrace_cost_le
    m 0 formula symbolCount hbudget
  have hfactor := fixitrQpowTraceFactor_le_polynomial m symbolCount
  have hsymbols : symbolCount <= codeLength := by
    exact formulaSymbolCount_le_binaryFormulaCode_length formula
  have harg : m + symbolCount + 1 <= m + codeLength + 1 := by omega
  have hpow := Nat.pow_le_pow_left harg 2
  have hpoly :
      fixitrQpowTraceFactor m symbolCount <=
        128 * (m + codeLength + 1) ^ 2 :=
    hfactor.trans (Nat.mul_le_mul_left 128 hpow)
  have hscaled := Nat.mul_le_mul_right codeLength hpoly
  exact htrace.trans (by
    simpa [binaryFormulaFixitrTrace, symbolCount, codeLength,
      Nat.mul_assoc] using hscaled)

/-! ## Honest construction of the successor-induction body -/

/-- Moving the free-variable namespace aside, performing the already traced
closed-target substitution, and then capturing free variable zero implements
an open-target one-variable substitution.  All three traversals are retained
in the cost coordinate. -/
def binaryFormulaOpenSubstitutionTrace
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat) :
    FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
      (LO.FirstOrder.ArithmeticSemiformula Nat 1) :=
  let shifted :=
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace
      1 body
  let substituted :=
    binaryFormulaSubstitutionOneTrace shifted.1 witness
  let fixed := binaryFormulaFixitrTrace 1 substituted.1
  (fixed.1, shifted.2 + substituted.2 + fixed.2 + 3)

/-- Term-level identity behind the open-substitution construction. -/
theorem fixitrOne_comp_substitution_comp_shift
    (witness : LO.FirstOrder.ArithmeticTerm Nat) :
    ((Rew.fixitr (L := ℒₒᵣ) 0 1).comp (Rew.subst ![witness])).comp
        (Rew.shift : Rew ℒₒᵣ Nat 1 Nat 1) =
      (Rew.subst ![
          (Rew.fixitr (L := ℒₒᵣ) 0 1) witness] :
        Rew ℒₒᵣ Nat 1 Nat 1) := by
  apply Rew.ext
  · intro index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    simp [Rew.comp_app]
  · intro index
    simp only [Rew.comp_app, Rew.shift_fvar, Rew.subst_fvar,
      Rew.fixitr_fvar]
    rw [dif_neg (by omega)]
    simp

theorem binaryFormulaOpenSubstitutionTrace_result
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat) :
    (binaryFormulaOpenSubstitutionTrace body witness).1 =
      Rewriting.app
        (Rew.subst ![
          (Rew.fixitr (L := ℒₒᵣ) 0 1) witness]) body := by
  simp only [binaryFormulaOpenSubstitutionTrace, Prod.fst]
  rw [binaryFormulaFixitrTrace_result,
    binaryFormulaSubstitutionOneTrace_result,
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace_result]
  change
    Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 1)
        (Rewriting.app (Rew.subst ![witness])
          (Rewriting.app Rew.shift body)) = _
  calc
    _ = Rewriting.app
          ((Rew.fixitr (L := ℒₒᵣ) 0 1).comp (Rew.subst ![witness]))
          (Rewriting.app Rew.shift body) := by
        symm
        exact TransitiveRewriting.comp_app _ _ _
    _ = Rewriting.app
          (((Rew.fixitr (L := ℒₒᵣ) 0 1).comp
            (Rew.subst ![witness])).comp
              (Rew.shift : Rew ℒₒᵣ Nat 1 Nat 1)) body := by
        symm
        exact TransitiveRewriting.comp_app _ _ _
    _ = _ := by rw [fixitrOne_comp_substitution_comp_shift]

theorem binaryFormulaOpenSubstitutionTrace_intermediate_code_le_of_witness
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat)
    (hwitness : (binaryTermCode witness).length <= 32) :
    let shifted :=
      FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace
        1 body
    let substituted :=
      binaryFormulaSubstitutionOneTrace shifted.1 witness
    (binaryFormulaCode shifted.1).length <=
        2 * (binaryFormulaCode body).length ∧
      (binaryFormulaCode substituted.1).length <=
        400 * ((binaryFormulaCode body).length + 1) ^ 2 := by
  dsimp only
  let shifted :=
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace
      1 body
  let substituted :=
    binaryFormulaSubstitutionOneTrace shifted.1 witness
  let inputLength := (binaryFormulaCode body).length
  let shiftedLength := (binaryFormulaCode shifted.1).length
  let substitutedLength := (binaryFormulaCode substituted.1).length
  let scale := inputLength + 1
  have hshift : shiftedLength <= 2 * inputLength := by
    dsimp [shiftedLength, shifted, inputLength]
    rw [FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace_result]
    exact binaryFormulaCode_shift_length_le body
  have hsubstitution :
      substitutedLength <=
        3 * (shiftedLength + 1) *
          ((binaryTermCode witness).length + 1) * shiftedLength := by
    dsimp [substitutedLength, substituted]
    rw [binaryFormulaSubstitutionOneTrace_result]
    exact binaryFormulaCode_substitution_one_length_le shifted.1 witness
  have hshiftScale : shiftedLength <= 2 * scale := by
    exact hshift.trans (Nat.mul_le_mul_left 2 (by
      dsimp [scale, inputLength]
      omega))
  have hshiftScaleOne : shiftedLength + 1 <= 2 * scale := by
    dsimp [scale, inputLength]
    omega
  have hwitnessOne : (binaryTermCode witness).length + 1 <= 33 := by
    omega
  have hproduct := Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul_left 3 hshiftScaleOne) hwitnessOne)
    hshiftScale
  have hsubstitutionScale :
      substitutedLength <= 400 * scale ^ 2 := by
    calc
      substitutedLength <=
          3 * (shiftedLength + 1) *
            ((binaryTermCode witness).length + 1) * shiftedLength :=
        hsubstitution
      _ <= 3 * (2 * scale) * 33 * (2 * scale) := hproduct
      _ = 396 * scale ^ 2 := by
        norm_num [pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ <= 400 * scale ^ 2 := by
        simpa [Nat.mul_comm] using
          Nat.mul_le_mul_left (scale ^ 2) (show 396 <= 400 by omega)
  simpa [shifted, substituted, inputLength, shiftedLength,
    substitutedLength, scale] using And.intro hshift hsubstitutionScale

theorem binaryFormulaOpenSubstitutionTrace_code_length_le_of_witness
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat)
    (hwitness : (binaryTermCode witness).length <= 32) :
    (binaryFormulaCode
      (binaryFormulaOpenSubstitutionTrace body witness).1).length <=
        1_000_000 * ((binaryFormulaCode body).length + 1) ^ 4 := by
  let shifted :=
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace
      1 body
  let substituted :=
    binaryFormulaSubstitutionOneTrace shifted.1 witness
  let substitutedLength := (binaryFormulaCode substituted.1).length
  let scale := (binaryFormulaCode body).length + 1
  have hintermediate :=
    binaryFormulaOpenSubstitutionTrace_intermediate_code_le_of_witness
      body witness hwitness
  have hsubstitution : substitutedLength <= 400 * scale ^ 2 := by
    simpa only [shifted, substituted, substitutedLength, scale] using
      hintermediate.2
  have hscaleOne : 1 <= scale ^ 2 := by
    have hscale : 1 <= scale := by
      dsimp [scale]
      omega
    simpa using Nat.pow_le_pow_left hscale 2
  have hsubstitutionOne :
      substitutedLength + 1 <= 401 * scale ^ 2 := by
    omega
  have hfixitr :=
    binaryFormulaFixitrTrace_code_length_le 1 substituted.1
  have hpow := Nat.pow_le_pow_left hsubstitutionOne 2
  have hscaled := Nat.mul_le_mul_left 4 hpow
  have hbound :
      (binaryFormulaCode
        (binaryFormulaFixitrTrace 1 substituted.1).1).length <=
          1_000_000 * scale ^ 4 := by
    calc
      (binaryFormulaCode
          (binaryFormulaFixitrTrace 1 substituted.1).1).length <=
          4 * (substitutedLength + 1) ^ 2 := by
        simpa only [substitutedLength] using hfixitr
      _ <= 4 * (401 * scale ^ 2) ^ 2 := hscaled
      _ = 643_204 * scale ^ 4 := by
        norm_num [pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ <= 1_000_000 * scale ^ 4 := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left (scale ^ 4)
          (show 643_204 <= 1_000_000 by omega)
  simpa [binaryFormulaOpenSubstitutionTrace, shifted, substituted,
    scale] using hbound

theorem binaryFormulaOpenSubstitutionTrace_cost_le_of_witness
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat)
    (hwitness : (binaryTermCode witness).length <= 32) :
    (binaryFormulaOpenSubstitutionTrace body witness).2 <=
      9_000_000_000 * ((binaryFormulaCode body).length + 1) ^ 6 := by
  let shifted :=
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace
      1 body
  let substituted :=
    binaryFormulaSubstitutionOneTrace shifted.1 witness
  let inputLength := (binaryFormulaCode body).length
  let shiftedLength := (binaryFormulaCode shifted.1).length
  let substitutedLength := (binaryFormulaCode substituted.1).length
  let scale := inputLength + 1
  have hscalePos : 0 < scale := by
    dsimp [scale, inputLength]
    omega
  have hscaleOne : 1 <= scale := hscalePos
  have hintermediate :=
    binaryFormulaOpenSubstitutionTrace_intermediate_code_le_of_witness
      body witness hwitness
  have hshiftCode : shiftedLength <= 2 * inputLength := by
    simpa only [shifted, substituted, inputLength, shiftedLength,
      substitutedLength, scale] using hintermediate.1
  have hsubstitutionCode :
      substitutedLength <= 400 * scale ^ 2 := by
    simpa only [shifted, substituted, inputLength, shiftedLength,
      substitutedLength, scale] using hintermediate.2
  have hshiftScale : shiftedLength <= 2 * scale := by
    exact hshiftCode.trans (Nat.mul_le_mul_left 2 (by
      dsimp [scale]
      omega))
  have hshiftScaleOne : shiftedLength + 1 <= 2 * scale := by
    dsimp [scale, inputLength]
    omega
  have hwitnessOne : (binaryTermCode witness).length + 1 <= 33 := by
    omega
  have hsymbolCount := formulaSymbolCount_le_binaryFormulaCode_length body
  have hshiftTrace :=
    FoundationCompactSyntaxTransformationTraceCore.binaryFormulaShiftQpowTrace_cost_le
      1 body (1 + formulaSymbolCount body) (by omega)
  have hshiftFactor :
      100 * (1 + formulaSymbolCount body + 1) <= 200 * scale := by
    dsimp [scale, inputLength]
    omega
  have hinputScale : inputLength <= scale := by
    dsimp [scale]
    omega
  have hshiftProduct := Nat.mul_le_mul hshiftFactor hinputScale
  have hshiftCost : shifted.2 <= 200 * scale ^ 2 := by
    exact hshiftTrace.trans (by
      simpa [shifted, inputLength, scale, pow_two,
        Nat.mul_assoc] using hshiftProduct)
  have hsubstitutionTrace :=
    binaryFormulaSubstitutionOneTrace_cost_le shifted.1 witness
  have hshiftPow := Nat.pow_le_pow_left hshiftScaleOne 2
  have hsubstitutionProduct := Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul_left 32 hshiftPow) hwitnessOne)
    hshiftScale
  have hsubstitutionCost :
      substituted.2 <= 8_448 * scale ^ 3 := by
    refine hsubstitutionTrace.trans ?_
    calc
      32 * (shiftedLength + 1) ^ 2 *
            ((binaryTermCode witness).length + 1) * shiftedLength <=
          32 * (2 * scale) ^ 2 * 33 * (2 * scale) :=
        hsubstitutionProduct
      _ = 8_448 * scale ^ 3 := by
        norm_num [pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  have hscaleSquare : 1 <= scale ^ 2 := by
    simpa using Nat.pow_le_pow_left hscaleOne 2
  have hsubstitutionTwo :
      1 + substitutedLength + 1 <= 402 * scale ^ 2 := by
    omega
  have hfixitrTrace :=
    binaryFormulaFixitrTrace_cost_le 1 substituted.1
  have hfixitrPow := Nat.pow_le_pow_left hsubstitutionTwo 2
  have hfixitrCost :
      (binaryFormulaFixitrTrace 1 substituted.1).2 <=
        8_274_124_800 * scale ^ 6 := by
    refine hfixitrTrace.trans ?_
    calc
      128 * (1 + substitutedLength + 1) ^ 2 * substitutedLength <=
          128 * (402 * scale ^ 2) ^ 2 * substitutedLength :=
        Nat.mul_le_mul_right substitutedLength
          (Nat.mul_le_mul_left 128 hfixitrPow)
      _ <= 128 * (402 * scale ^ 2) ^ 2 * (400 * scale ^ 2) :=
        Nat.mul_le_mul_left (128 * (402 * scale ^ 2) ^ 2)
          hsubstitutionCode
      _ = 8_274_124_800 * scale ^ 6 := by
        norm_num [pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  have hpowTwoSix : scale ^ 2 <= scale ^ 6 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hpowThreeSix : scale ^ 3 <= scale ^ 6 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hpowSixOne : 1 <= scale ^ 6 := by
    simpa using Nat.pow_le_pow_left hscaleOne 6
  have hshiftCost' : shifted.2 <= 200 * scale ^ 6 :=
    hshiftCost.trans (Nat.mul_le_mul_left 200 hpowTwoSix)
  have hsubstitutionCost' : substituted.2 <= 8_448 * scale ^ 6 :=
    hsubstitutionCost.trans (Nat.mul_le_mul_left 8_448 hpowThreeSix)
  have hbound :
      shifted.2 + substituted.2 +
          (binaryFormulaFixitrTrace 1 substituted.1).2 + 3 <=
        9_000_000_000 * scale ^ 6 := by
    have hthree : 3 <= 3 * scale ^ 6 :=
      Nat.mul_le_mul_left 3 hpowSixOne
    omega
  simpa [binaryFormulaOpenSubstitutionTrace, shifted, substituted,
    inputLength, scale] using hbound

def succIndZeroWitness : LO.FirstOrder.ArithmeticTerm Nat :=
  (‘0’ : LO.FirstOrder.ArithmeticTerm Nat)

def succIndOpenZeroWitness : LO.FirstOrder.ArithmeticTerm Nat :=
  (&0 : LO.FirstOrder.ArithmeticTerm Nat)

def succIndOpenSuccessorWitness : LO.FirstOrder.ArithmeticTerm Nat :=
  (‘&0 + 1’ : LO.FirstOrder.ArithmeticTerm Nat)

theorem succIndZeroWitness_code_length_le :
    (binaryTermCode succIndZeroWitness).length <= 32 := by
  decide

theorem succIndOpenZeroWitness_code_length_le :
    (binaryTermCode succIndOpenZeroWitness).length <= 32 := by
  decide

theorem succIndOpenSuccessorWitness_code_length_le :
    (binaryTermCode succIndOpenSuccessorWitness).length <= 32 := by
  decide

def binaryFormulaOpenZeroSubstitutionTrace
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
      (LO.FirstOrder.ArithmeticSemiformula Nat 1) :=
  binaryFormulaOpenSubstitutionTrace body succIndOpenZeroWitness

def binaryFormulaOpenSuccessorSubstitutionTrace
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
      (LO.FirstOrder.ArithmeticSemiformula Nat 1) :=
  binaryFormulaOpenSubstitutionTrace body succIndOpenSuccessorWitness

theorem binaryFormulaOpenZeroSubstitutionTrace_result
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaOpenZeroSubstitutionTrace body).1 =
      Rewriting.app
        (Rew.subst ![(#0 :
          LO.FirstOrder.ArithmeticSemiterm Nat 1)]) body := by
  rw [binaryFormulaOpenZeroSubstitutionTrace,
    binaryFormulaOpenSubstitutionTrace_result]
  have hw :
      (Rew.fixitr (L := ℒₒᵣ) 0 1) succIndOpenZeroWitness =
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
    simp only [succIndOpenZeroWitness, Rew.fixitr_fvar]
    rw [dif_pos (by omega)]
    congr
  rw [hw]

theorem binaryFormulaOpenSuccessorSubstitutionTrace_result
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaOpenSuccessorSubstitutionTrace body).1 =
      Rewriting.app
        (Rew.subst ![(‘#0 + 1’ :
          LO.FirstOrder.ArithmeticSemiterm Nat 1)]) body := by
  rw [binaryFormulaOpenSuccessorSubstitutionTrace,
    binaryFormulaOpenSubstitutionTrace_result]
  have hzero :
      (Rew.fixitr (L := ℒₒᵣ) 0 1)
          (&0 : LO.FirstOrder.ArithmeticTerm Nat) =
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
    simp only [Rew.fixitr_fvar]
    rw [dif_pos (by omega)]
    congr
  have hw :
      (Rew.fixitr (L := ℒₒᵣ) 0 1) succIndOpenSuccessorWitness =
        (‘#0 + 1’ : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
    simp [succIndOpenSuccessorWitness, Semiterm.Operator.operator,
      Semiterm.Operator.Add.term_eq, Semiterm.Operator.One.term_eq,
      Rew.emb_eq_id, Rew.func, hzero]
    funext index
    cases index using Fin.cases with
    | zero => simpa using hzero
    | succ index =>
        have hindex : index = 0 := Fin.eq_zero index
        subst index
        simp only [Function.comp_apply, Rew.emb_bvar, Rew.subst_bvar,
          Matrix.cons_val_one]
        apply Semiterm.rew_eq_of_funEqOn
        · intro index
          exact Fin.elim0 index
        · intro index hindex
          simpa [Semiterm.FVar?, Semiterm.freeVariables_emb] using hindex
  rw [hw]

theorem binaryFormulaOpenZeroSubstitutionTrace_code_length_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode
      (binaryFormulaOpenZeroSubstitutionTrace body).1).length <=
        1_000_000 * ((binaryFormulaCode body).length + 1) ^ 4 := by
  simpa only [binaryFormulaOpenZeroSubstitutionTrace] using
    binaryFormulaOpenSubstitutionTrace_code_length_le_of_witness
      body succIndOpenZeroWitness succIndOpenZeroWitness_code_length_le

theorem binaryFormulaOpenSuccessorSubstitutionTrace_code_length_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode
      (binaryFormulaOpenSuccessorSubstitutionTrace body).1).length <=
        1_000_000 * ((binaryFormulaCode body).length + 1) ^ 4 := by
  simpa only [binaryFormulaOpenSuccessorSubstitutionTrace] using
    binaryFormulaOpenSubstitutionTrace_code_length_le_of_witness
      body succIndOpenSuccessorWitness
        succIndOpenSuccessorWitness_code_length_le

theorem binaryFormulaOpenZeroSubstitutionTrace_cost_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaOpenZeroSubstitutionTrace body).2 <=
      9_000_000_000 * ((binaryFormulaCode body).length + 1) ^ 6 := by
  simpa only [binaryFormulaOpenZeroSubstitutionTrace] using
    binaryFormulaOpenSubstitutionTrace_cost_le_of_witness
      body succIndOpenZeroWitness succIndOpenZeroWitness_code_length_le

theorem binaryFormulaOpenSuccessorSubstitutionTrace_cost_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaOpenSuccessorSubstitutionTrace body).2 <=
      9_000_000_000 * ((binaryFormulaCode body).length + 1) ^ 6 := by
  simpa only [binaryFormulaOpenSuccessorSubstitutionTrace] using
    binaryFormulaOpenSubstitutionTrace_cost_le_of_witness
      body succIndOpenSuccessorWitness
        succIndOpenSuccessorWitness_code_length_le

theorem binarySuccIndBaseTrace_code_length_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode
      (binaryFormulaSubstitutionOneTrace body succIndZeroWitness).1).length <=
        100 * ((binaryFormulaCode body).length + 1) ^ 2 := by
  let inputLength := (binaryFormulaCode body).length
  let scale := inputLength + 1
  have htrace :
      (binaryFormulaCode
        (binaryFormulaSubstitutionOneTrace body succIndZeroWitness).1).length <=
          3 * (inputLength + 1) *
            ((binaryTermCode succIndZeroWitness).length + 1) *
              inputLength := by
    rw [binaryFormulaSubstitutionOneTrace_result]
    simpa only [inputLength] using
      binaryFormulaCode_substitution_one_length_le
        body succIndZeroWitness
  have hwitness :
      (binaryTermCode succIndZeroWitness).length + 1 <= 33 := by
    have hw := succIndZeroWitness_code_length_le
    omega
  have hinput : inputLength <= scale := by
    dsimp [scale]
    omega
  have hproduct := Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul_left 3 (show inputLength + 1 <= scale by rfl))
      hwitness) hinput
  refine htrace.trans ?_
  calc
    3 * (inputLength + 1) *
          ((binaryTermCode succIndZeroWitness).length + 1) * inputLength <=
        3 * scale * 33 * scale := hproduct
    _ = 99 * scale ^ 2 := by
      norm_num [pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    _ <= 100 * scale ^ 2 := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (scale ^ 2)
        (show 99 <= 100 by omega)

theorem binarySuccIndBaseTrace_cost_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaSubstitutionOneTrace body succIndZeroWitness).2 <=
      2_000 * ((binaryFormulaCode body).length + 1) ^ 3 := by
  let inputLength := (binaryFormulaCode body).length
  let scale := inputLength + 1
  have htrace :=
    binaryFormulaSubstitutionOneTrace_cost_le body succIndZeroWitness
  have hwitness :
      (binaryTermCode succIndZeroWitness).length + 1 <= 33 := by
    have hw := succIndZeroWitness_code_length_le
    omega
  have hinput : inputLength <= scale := by
    dsimp [scale]
    omega
  have hpow := Nat.pow_le_pow_left
    (show inputLength + 1 <= scale by rfl) 2
  have hproduct := Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul_left 32 hpow) hwitness) hinput
  refine htrace.trans ?_
  calc
    32 * (inputLength + 1) ^ 2 *
          ((binaryTermCode succIndZeroWitness).length + 1) * inputLength <=
        32 * scale ^ 2 * 33 * scale := hproduct
    _ = 1_056 * scale ^ 3 := by
      norm_num [pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    _ <= 2_000 * scale ^ 3 := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (scale ^ 3)
        (show 1_056 <= 2_000 by omega)

/-- Charge the construction of all four substitution witnesses.  The open
zero witness occurs twice because the step premise and final conclusion are
separate substitution executions. -/
def succIndWitnessConstructionCost : Nat :=
  (binaryTermCode succIndZeroWitness).length +
    2 * (binaryTermCode succIndOpenZeroWitness).length +
    (binaryTermCode succIndOpenSuccessorWitness).length + 4

/-- Construct `succInd body` without sharing away any of its four formula
substitutions.  Implication is constructed by its actual `neg/or` syntax. -/
def binarySuccIndTrace
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    FoundationCompactSyntaxTransformationTraceCore.SyntaxTrace
      LO.FirstOrder.ArithmeticProposition :=
  let base := binaryFormulaSubstitutionOneTrace body succIndZeroWitness
  let stepZero := binaryFormulaOpenZeroSubstitutionTrace body
  let stepSuccessor := binaryFormulaOpenSuccessorSubstitutionTrace body
  let finalZero := binaryFormulaOpenZeroSubstitutionTrace body
  let negStepZero := binaryFormulaNegTrace stepZero.1
  let stepImplication := negStepZero.1 ⋎ stepSuccessor.1
  let quantifiedStep := ∀⁰ stepImplication
  let negQuantifiedStep := binaryFormulaNegTrace quantifiedStep
  let quantifiedFinal := ∀⁰ finalZero.1
  let negBase := binaryFormulaNegTrace base.1
  (negBase.1 ⋎ (negQuantifiedStep.1 ⋎ quantifiedFinal),
    succIndWitnessConstructionCost +
      base.2 + stepZero.2 + stepSuccessor.2 + finalZero.2 +
      negStepZero.2 + negQuantifiedStep.2 + negBase.2 +
      3 * (2 *
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5 + 3) +
      2 * (2 *
        FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6 + 3))

theorem binarySuccIndTrace_result
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binarySuccIndTrace body).1 = succInd body := by
  simp only [binarySuccIndTrace, Prod.fst]
  rw [binaryFormulaSubstitutionOneTrace_result,
    binaryFormulaOpenZeroSubstitutionTrace_result,
    binaryFormulaOpenSuccessorSubstitutionTrace_result]
  simp only [binaryFormulaNegTrace_result]
  simp [succInd, Semiformula.imp_eq, succIndZeroWitness]

theorem binarySuccIndTrace_code_length_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode (binarySuccIndTrace body).1).length <=
      10_000_000 * ((binaryFormulaCode body).length + 1) ^ 4 := by
  let base := binaryFormulaSubstitutionOneTrace body succIndZeroWitness
  let stepZero := binaryFormulaOpenZeroSubstitutionTrace body
  let stepSuccessor := binaryFormulaOpenSuccessorSubstitutionTrace body
  let finalZero := binaryFormulaOpenZeroSubstitutionTrace body
  let negStepZero := binaryFormulaNegTrace stepZero.1
  let stepImplication := negStepZero.1 ⋎ stepSuccessor.1
  let quantifiedStep := ∀⁰ stepImplication
  let negQuantifiedStep := binaryFormulaNegTrace quantifiedStep
  let quantifiedFinal := ∀⁰ finalZero.1
  let negBase := binaryFormulaNegTrace base.1
  let scale := (binaryFormulaCode body).length + 1
  have hscalePos : 0 < scale := by
    dsimp [scale]
    omega
  have hscaleOne : 1 <= scale := hscalePos
  have hpowTwoFour : scale ^ 2 <= scale ^ 4 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hpowFourOne : 1 <= scale ^ 4 := by
    simpa using Nat.pow_le_pow_left hscaleOne 4
  have hbase : (binaryFormulaCode base.1).length <=
      100 * scale ^ 2 := by
    simpa only [base, scale] using binarySuccIndBaseTrace_code_length_le body
  have hbaseFour : (binaryFormulaCode base.1).length <=
      100 * scale ^ 4 :=
    hbase.trans (Nat.mul_le_mul_left 100 hpowTwoFour)
  have hstepZero : (binaryFormulaCode stepZero.1).length <=
      1_000_000 * scale ^ 4 := by
    simpa only [stepZero, scale] using
      binaryFormulaOpenZeroSubstitutionTrace_code_length_le body
  have hstepSuccessor :
      (binaryFormulaCode stepSuccessor.1).length <=
        1_000_000 * scale ^ 4 := by
    simpa only [stepSuccessor, scale] using
      binaryFormulaOpenSuccessorSubstitutionTrace_code_length_le body
  have hfinalZero : (binaryFormulaCode finalZero.1).length <=
      1_000_000 * scale ^ 4 := by
    simpa only [finalZero, scale] using
      binaryFormulaOpenZeroSubstitutionTrace_code_length_le body
  have hnegStepZero :
      (binaryFormulaCode negStepZero.1).length <=
        2_000_000 * scale ^ 4 := by
    have hneg := binaryFormulaCode_neg_length_le stepZero.1
    have hneg' :
        (binaryFormulaCode negStepZero.1).length <=
          2 * (binaryFormulaCode stepZero.1).length := by
      simpa only [negStepZero, binaryFormulaNegTrace_result] using hneg
    exact hneg'.trans (by omega)
  have hheaderFive : (binaryNatCode 5).length <= 10 := by
    decide
  have hheaderSix : (binaryNatCode 6).length <= 10 := by
    decide
  have hstepImplication :
      (binaryFormulaCode stepImplication).length <=
        3_100_000 * scale ^ 4 := by
    simp only [stepImplication, binaryFormulaCode, List.length_append]
    omega
  have hquantifiedStep :
      (binaryFormulaCode quantifiedStep).length <=
        3_200_000 * scale ^ 4 := by
    simp only [quantifiedStep, binaryFormulaCode, List.length_append]
    omega
  have hnegQuantifiedStep :
      (binaryFormulaCode negQuantifiedStep.1).length <=
        6_400_000 * scale ^ 4 := by
    have hneg := binaryFormulaCode_neg_length_le quantifiedStep
    have hneg' :
        (binaryFormulaCode negQuantifiedStep.1).length <=
          2 * (binaryFormulaCode quantifiedStep).length := by
      simpa only [negQuantifiedStep, binaryFormulaNegTrace_result] using hneg
    exact hneg'.trans (by omega)
  have hquantifiedFinal :
      (binaryFormulaCode quantifiedFinal).length <=
        1_100_000 * scale ^ 4 := by
    simp only [quantifiedFinal, binaryFormulaCode, List.length_append]
    omega
  have hnegBase :
      (binaryFormulaCode negBase.1).length <= 200 * scale ^ 4 := by
    have hneg := binaryFormulaCode_neg_length_le base.1
    have hneg' :
        (binaryFormulaCode negBase.1).length <=
          2 * (binaryFormulaCode base.1).length := by
      simpa only [negBase, binaryFormulaNegTrace_result] using hneg
    exact hneg'.trans (by omega)
  change
    (binaryFormulaCode
      (negBase.1 ⋎ (negQuantifiedStep.1 ⋎ quantifiedFinal))).length <=
        10_000_000 * scale ^ 4
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binarySuccIndTrace_cost_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binarySuccIndTrace body).2 <=
      100_000_000_000 * ((binaryFormulaCode body).length + 1) ^ 12 := by
  let base := binaryFormulaSubstitutionOneTrace body succIndZeroWitness
  let stepZero := binaryFormulaOpenZeroSubstitutionTrace body
  let stepSuccessor := binaryFormulaOpenSuccessorSubstitutionTrace body
  let finalZero := binaryFormulaOpenZeroSubstitutionTrace body
  let negStepZero := binaryFormulaNegTrace stepZero.1
  let stepImplication := negStepZero.1 ⋎ stepSuccessor.1
  let quantifiedStep := ∀⁰ stepImplication
  let negQuantifiedStep := binaryFormulaNegTrace quantifiedStep
  let quantifiedFinal := ∀⁰ finalZero.1
  let negBase := binaryFormulaNegTrace base.1
  let scale := (binaryFormulaCode body).length + 1
  have hscalePos : 0 < scale := by
    dsimp [scale]
    omega
  have hscaleOne : 1 <= scale := hscalePos
  have hpowFourOne : 1 <= scale ^ 4 := by
    simpa using Nat.pow_le_pow_left hscaleOne 4
  have hpowTwoTwelve : scale ^ 2 <= scale ^ 12 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hpowThreeTwelve : scale ^ 3 <= scale ^ 12 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hpowFourTwelve : scale ^ 4 <= scale ^ 12 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hpowSixTwelve : scale ^ 6 <= scale ^ 12 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hpowTwelveOne : 1 <= scale ^ 12 := by
    simpa using Nat.pow_le_pow_left hscaleOne 12
  have hbaseCode : (binaryFormulaCode base.1).length <=
      100 * scale ^ 2 := by
    simpa only [base, scale] using binarySuccIndBaseTrace_code_length_le body
  have hstepZeroCode : (binaryFormulaCode stepZero.1).length <=
      1_000_000 * scale ^ 4 := by
    simpa only [stepZero, scale] using
      binaryFormulaOpenZeroSubstitutionTrace_code_length_le body
  have hquantifiedStepCode :
      (binaryFormulaCode quantifiedStep).length <=
        3_200_000 * scale ^ 4 := by
    have hneg :
        (binaryFormulaCode negStepZero.1).length <=
          2 * (binaryFormulaCode stepZero.1).length := by
      simpa only [negStepZero, binaryFormulaNegTrace_result] using
        binaryFormulaCode_neg_length_le stepZero.1
    have hsuccessor :
        (binaryFormulaCode stepSuccessor.1).length <=
          1_000_000 * scale ^ 4 := by
      simpa only [stepSuccessor, scale] using
        binaryFormulaOpenSuccessorSubstitutionTrace_code_length_le body
    have hheaderFive : (binaryNatCode 5).length <= 10 := by
      decide
    have hheaderSix : (binaryNatCode 6).length <= 10 := by
      decide
    simp only [quantifiedStep, stepImplication, binaryFormulaCode,
      List.length_append]
    omega
  have hbaseCost : base.2 <= 2_000 * scale ^ 3 := by
    simpa only [base, scale] using binarySuccIndBaseTrace_cost_le body
  have hstepZeroCost : stepZero.2 <= 9_000_000_000 * scale ^ 6 := by
    simpa only [stepZero, scale] using
      binaryFormulaOpenZeroSubstitutionTrace_cost_le body
  have hstepSuccessorCost :
      stepSuccessor.2 <= 9_000_000_000 * scale ^ 6 := by
    simpa only [stepSuccessor, scale] using
      binaryFormulaOpenSuccessorSubstitutionTrace_cost_le body
  have hfinalZeroCost : finalZero.2 <= 9_000_000_000 * scale ^ 6 := by
    simpa only [finalZero, scale] using
      binaryFormulaOpenZeroSubstitutionTrace_cost_le body
  have hnegStepZeroCost : negStepZero.2 <=
      1_000_000 * scale ^ 4 := by
    exact (binaryFormulaNegTrace_cost_le stepZero.1).trans hstepZeroCode
  have hnegQuantifiedStepCost : negQuantifiedStep.2 <=
      3_200_000 * scale ^ 4 := by
    exact (binaryFormulaNegTrace_cost_le quantifiedStep).trans
      hquantifiedStepCode
  have hnegBaseCost : negBase.2 <= 100 * scale ^ 2 := by
    exact (binaryFormulaNegTrace_cost_le base.1).trans hbaseCode
  have hbookkeeping :
      succIndWitnessConstructionCost +
        3 * (2 *
          FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5 + 3) +
        2 * (2 *
          FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6 + 3) <=
        1_000 := by
    decide
  have hbaseCost' : base.2 <= 2_000 * scale ^ 12 :=
    hbaseCost.trans (Nat.mul_le_mul_left 2_000 hpowThreeTwelve)
  have hstepZeroCost' : stepZero.2 <=
      9_000_000_000 * scale ^ 12 :=
    hstepZeroCost.trans (Nat.mul_le_mul_left 9_000_000_000 hpowSixTwelve)
  have hstepSuccessorCost' : stepSuccessor.2 <=
      9_000_000_000 * scale ^ 12 :=
    hstepSuccessorCost.trans
      (Nat.mul_le_mul_left 9_000_000_000 hpowSixTwelve)
  have hfinalZeroCost' : finalZero.2 <=
      9_000_000_000 * scale ^ 12 :=
    hfinalZeroCost.trans
      (Nat.mul_le_mul_left 9_000_000_000 hpowSixTwelve)
  have hnegStepZeroCost' : negStepZero.2 <=
      1_000_000 * scale ^ 12 :=
    hnegStepZeroCost.trans
      (Nat.mul_le_mul_left 1_000_000 hpowFourTwelve)
  have hnegQuantifiedStepCost' : negQuantifiedStep.2 <=
      3_200_000 * scale ^ 12 :=
    hnegQuantifiedStepCost.trans
      (Nat.mul_le_mul_left 3_200_000 hpowFourTwelve)
  have hnegBaseCost' : negBase.2 <= 100 * scale ^ 12 :=
    hnegBaseCost.trans (Nat.mul_le_mul_left 100 hpowTwoTwelve)
  have hbookkeeping' :
      succIndWitnessConstructionCost +
        3 * (2 *
          FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5 + 3) +
        2 * (2 *
          FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6 + 3) <=
        1_000 * scale ^ 12 :=
    hbookkeeping.trans (Nat.mul_le_mul_left 1_000 hpowTwelveOne)
  change
    succIndWitnessConstructionCost +
        base.2 + stepZero.2 + stepSuccessor.2 + finalZero.2 +
        negStepZero.2 + negQuantifiedStep.2 + negBase.2 +
        3 * (2 *
          FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 5 + 3) +
        2 * (2 *
          FoundationCompactSyntaxTransformationTraceCore.binaryFormulaNodeHeaderCost 6 + 3) <=
      100_000_000_000 * scale ^ 12
  omega

/-! ## Guarded PA-axiom sentence comparison -/

/-- Compare an explicitly constructed sentence with the candidate, charging
the complete generated code once more for construction in addition to the
code-emission and bit-comparison costs already charged by `formulaEqTrace`. -/
def constructedSentenceEqTrace
    (generated candidate : LO.FirstOrder.ArithmeticSentence) : Bool × Nat :=
  let generatedFormula :=
    (Rewriting.emb generated : LO.FirstOrder.ArithmeticProposition)
  let candidateFormula :=
    (Rewriting.emb candidate : LO.FirstOrder.ArithmeticProposition)
  let comparison := formulaEqTrace generatedFormula candidateFormula
  (comparison.1,
    comparison.2 + (binaryFormulaCode generatedFormula).length + 1)

theorem constructedSentenceEqTrace_result_eq_true_iff
    (generated candidate : LO.FirstOrder.ArithmeticSentence) :
    (constructedSentenceEqTrace generated candidate).1 = true ↔
      generated = candidate := by
  rw [constructedSentenceEqTrace,
    formulaEqTrace_result_eq_true_iff]
  exact Rewriting.emb_injective.eq_iff

theorem constructedSentenceEqTrace_cost_le
    (generated candidate : LO.FirstOrder.ArithmeticSentence) :
    (constructedSentenceEqTrace generated candidate).2 <=
      3 * (binaryFormulaCode
          (Rewriting.emb generated :
            LO.FirstOrder.ArithmeticProposition)).length +
        (binaryFormulaCode
          (Rewriting.emb candidate :
            LO.FirstOrder.ArithmeticProposition)).length + 3 := by
  have hcomparison := formulaEqTrace_cost_le
    (Rewriting.emb generated : LO.FirstOrder.ArithmeticProposition)
    (Rewriting.emb candidate : LO.FirstOrder.ArithmeticProposition)
  simp only [constructedSentenceEqTrace]
  omega

def FixedPAAxiomCertificate : PAAxiomCertificate -> Prop
  | .induction _ => False
  | _ => True

/-- All non-induction cases are enumerated explicitly.  In particular, this
never dispatches through `PAAxiomCertificate.sentence`.  The 22 non-induction
constructor tags expand to finitely many constant cases in the fixed language. -/
def fixedAxiomSentenceEqTrace
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) : Bool × Nat :=
  match certificate with
  | .eqRefl =>
      constructedSentenceEqTrace
        (LO.FirstOrder.Theory.Eq.refl ℒₒᵣ) candidate
  | .eqSymm =>
      constructedSentenceEqTrace
        (LO.FirstOrder.Theory.Eq.symm ℒₒᵣ) candidate
  | .eqTrans =>
      constructedSentenceEqTrace
        (LO.FirstOrder.Theory.Eq.trans ℒₒᵣ) candidate
  | .eqFuncExt functionSymbol =>
      constructedSentenceEqTrace
        (LO.FirstOrder.Theory.Eq.funcExt functionSymbol) candidate
  | .eqRelExt relationSymbol =>
      constructedSentenceEqTrace
        (LO.FirstOrder.Theory.Eq.relExt relationSymbol) candidate
  | .addZero =>
      constructedSentenceEqTrace PeanoMinus.Axiom.addZero candidate
  | .addAssoc =>
      constructedSentenceEqTrace PeanoMinus.Axiom.addAssoc candidate
  | .addComm =>
      constructedSentenceEqTrace PeanoMinus.Axiom.addComm candidate
  | .addEqOfLt =>
      constructedSentenceEqTrace PeanoMinus.Axiom.addEqOfLt candidate
  | .zeroLe =>
      constructedSentenceEqTrace PeanoMinus.Axiom.zeroLe candidate
  | .zeroLtOne =>
      constructedSentenceEqTrace PeanoMinus.Axiom.zeroLtOne candidate
  | .oneLeOfZeroLt =>
      constructedSentenceEqTrace PeanoMinus.Axiom.oneLeOfZeroLt candidate
  | .addLtAdd =>
      constructedSentenceEqTrace PeanoMinus.Axiom.addLtAdd candidate
  | .mulZero =>
      constructedSentenceEqTrace PeanoMinus.Axiom.mulZero candidate
  | .mulOne =>
      constructedSentenceEqTrace PeanoMinus.Axiom.mulOne candidate
  | .mulAssoc =>
      constructedSentenceEqTrace PeanoMinus.Axiom.mulAssoc candidate
  | .mulComm =>
      constructedSentenceEqTrace PeanoMinus.Axiom.mulComm candidate
  | .mulLtMul =>
      constructedSentenceEqTrace PeanoMinus.Axiom.mulLtMul candidate
  | .distr =>
      constructedSentenceEqTrace PeanoMinus.Axiom.distr candidate
  | .ltIrrefl =>
      constructedSentenceEqTrace PeanoMinus.Axiom.ltIrrefl candidate
  | .ltTrans =>
      constructedSentenceEqTrace PeanoMinus.Axiom.ltTrans candidate
  | .ltTri =>
      constructedSentenceEqTrace PeanoMinus.Axiom.ltTri candidate
  | .induction _ => (false, 1)

theorem fixedAxiomSentenceEqTrace_result_eq_true_iff
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hfixed : FixedPAAxiomCertificate certificate) :
    (fixedAxiomSentenceEqTrace certificate candidate).1 = true ↔
      certificate.sentence = candidate := by
  cases certificate <;>
    simp [FixedPAAxiomCertificate, fixedAxiomSentenceEqTrace,
      PAAxiomCertificate.sentence,
      constructedSentenceEqTrace_result_eq_true_iff] at hfixed ⊢

def candidateSentenceCodeLength
    (candidate : LO.FirstOrder.ArithmeticSentence) : Nat :=
  (binaryFormulaCode
    (Rewriting.emb candidate :
      LO.FirstOrder.ArithmeticProposition)).length

/-- A literal constant budget containing all 26 concrete fixed PA/equality
sentences: 20 nonparameterized sentences and the six extensionality instances
of the fixed arithmetic language.  Using the sum avoids an opaque maximum and
makes each branch bound a direct arithmetic projection. -/
def constantAxiomSentenceCodeBudget : Nat :=
  candidateSentenceCodeLength (LO.FirstOrder.Theory.Eq.refl ℒₒᵣ) +
  candidateSentenceCodeLength (LO.FirstOrder.Theory.Eq.symm ℒₒᵣ) +
  candidateSentenceCodeLength (LO.FirstOrder.Theory.Eq.trans ℒₒᵣ) +
  candidateSentenceCodeLength
    (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.zero) +
  candidateSentenceCodeLength
    (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.one) +
  candidateSentenceCodeLength
    (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.add) +
  candidateSentenceCodeLength
    (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.mul) +
  candidateSentenceCodeLength
    (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.eq) +
  candidateSentenceCodeLength
    (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.lt) +
  candidateSentenceCodeLength PeanoMinus.Axiom.addZero +
  candidateSentenceCodeLength PeanoMinus.Axiom.addAssoc +
  candidateSentenceCodeLength PeanoMinus.Axiom.addComm +
  candidateSentenceCodeLength PeanoMinus.Axiom.addEqOfLt +
  candidateSentenceCodeLength PeanoMinus.Axiom.zeroLe +
  candidateSentenceCodeLength PeanoMinus.Axiom.zeroLtOne +
  candidateSentenceCodeLength PeanoMinus.Axiom.oneLeOfZeroLt +
  candidateSentenceCodeLength PeanoMinus.Axiom.addLtAdd +
  candidateSentenceCodeLength PeanoMinus.Axiom.mulZero +
  candidateSentenceCodeLength PeanoMinus.Axiom.mulOne +
  candidateSentenceCodeLength PeanoMinus.Axiom.mulAssoc +
  candidateSentenceCodeLength PeanoMinus.Axiom.mulComm +
  candidateSentenceCodeLength PeanoMinus.Axiom.mulLtMul +
  candidateSentenceCodeLength PeanoMinus.Axiom.distr +
  candidateSentenceCodeLength PeanoMinus.Axiom.ltIrrefl +
  candidateSentenceCodeLength PeanoMinus.Axiom.ltTrans +
  candidateSentenceCodeLength PeanoMinus.Axiom.ltTri

theorem fixedAxiomSentenceEqTrace_cost_le_constant
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hfixed : FixedPAAxiomCertificate certificate) :
    (fixedAxiomSentenceEqTrace certificate candidate).2 <=
      3 * constantAxiomSentenceCodeBudget +
        candidateSentenceCodeLength candidate + 3 := by
  cases certificate <;>
    simp [FixedPAAxiomCertificate] at hfixed
  case eqFuncExt functionSymbol =>
    cases functionSymbol <;>
      simp only [fixedAxiomSentenceEqTrace] <;>
      refine (constructedSentenceEqTrace_cost_le _ candidate).trans ?_ <;>
      unfold constantAxiomSentenceCodeBudget candidateSentenceCodeLength <;>
      omega
  case eqRelExt relationSymbol =>
    cases relationSymbol <;>
      simp only [fixedAxiomSentenceEqTrace] <;>
      refine (constructedSentenceEqTrace_cost_le _ candidate).trans ?_ <;>
      unfold constantAxiomSentenceCodeBudget candidateSentenceCodeLength <;>
      omega
  all_goals
    simp only [fixedAxiomSentenceEqTrace]
    refine (constructedSentenceEqTrace_cost_le _ candidate).trans ?_
    unfold constantAxiomSentenceCodeBudget candidateSentenceCodeLength
    omega

theorem fixedAxiomSentenceEqTrace_cost_le
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hfixed : FixedPAAxiomCertificate certificate) :
    (fixedAxiomSentenceEqTrace certificate candidate).2 <=
      (3 * constantAxiomSentenceCodeBudget + 4) *
          ((binaryPAAxiomCertificateCode certificate).length +
            candidateSentenceCodeLength candidate + 1) ^ 8 +
        candidateSentenceCodeLength candidate := by
  have hcost := fixedAxiomSentenceEqTrace_cost_le_constant
    certificate candidate hfixed
  have hbase :
      1 <= (binaryPAAxiomCertificateCode certificate).length +
        candidateSentenceCodeLength candidate + 1 := by omega
  have hpow :
      1 <= ((binaryPAAxiomCertificateCode certificate).length +
        candidateSentenceCodeLength candidate + 1) ^ 8 := by
    have := Nat.pow_le_pow_left hbase 8
    simpa using this
  have hscaled := Nat.mul_le_mul_left
    (3 * constantAxiomSentenceCodeBudget + 4) hpow
  omega

def inductionSentenceGuardTrace
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) : Bool × Nat :=
  let generated := binarySuccIndTrace body
  let depth := binaryFormulaFvSupTrace generated.1
  let candidateLength := candidateSentenceCodeLength candidate
  let comparison := binaryNatLeTrace depth.1 candidateLength
  (comparison.1,
    generated.2 + depth.2 + comparison.2 +
      (binaryFormulaCode body).length + candidateLength + 5)

theorem inductionSentenceGuardTrace_result_eq_true_iff
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    (inductionSentenceGuardTrace body candidate).1 = true ↔
      (succInd body).fvSup <= candidateSentenceCodeLength candidate := by
  simp only [inductionSentenceGuardTrace, Prod.fst]
  rw [binaryNatLeTrace_result_eq_true_iff,
    binaryFormulaFvSupTrace_result, binarySuccIndTrace_result]

theorem inductionSentenceGuardTrace_cost_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    let scale := (binaryFormulaCode body).length +
      candidateSentenceCodeLength candidate + 1
    (inductionSentenceGuardTrace body candidate).2 <=
      100_000_000_000_000_000_000_000_000 * scale ^ 12 := by
  let generated := binarySuccIndTrace body
  let depth := binaryFormulaFvSupTrace generated.1
  let candidateLength := candidateSentenceCodeLength candidate
  let comparison := binaryNatLeTrace depth.1 candidateLength
  let bodyLength := (binaryFormulaCode body).length
  let scale := bodyLength + candidateLength + 1
  have hscalePos : 0 < scale := by
    dsimp [scale]
    omega
  have hscaleOne : 1 <= scale := hscalePos
  have hbodyScale : bodyLength + 1 <= scale := by
    dsimp [scale]
    omega
  have hcandidateScale : candidateLength <= scale := by
    dsimp [scale]
    omega
  have hpowFourOne : 1 <= scale ^ 4 := by
    simpa using Nat.pow_le_pow_left hscaleOne 4
  have hpowTwelveOne : 1 <= scale ^ 12 := by
    simpa using Nat.pow_le_pow_left hscaleOne 12
  have hscaleFour : scale <= scale ^ 4 := by
    have := Nat.pow_le_pow_right hscalePos (show 1 <= 4 by omega)
    simpa using this
  have hgeneratedCode :
      (binaryFormulaCode generated.1).length <=
        10_000_000 * scale ^ 4 := by
    have hraw := binarySuccIndTrace_code_length_le body
    have hpow := Nat.pow_le_pow_left hbodyScale 4
    exact hraw.trans (Nat.mul_le_mul_left 10_000_000 hpow)
  have hgeneratedCodeOne :
      (binaryFormulaCode generated.1).length + 1 <=
        10_000_001 * scale ^ 4 := by
    omega
  have hgeneratedCost :
      generated.2 <= 100_000_000_000 * scale ^ 12 := by
    have hraw := binarySuccIndTrace_cost_le body
    have hpow := Nat.pow_le_pow_left hbodyScale 12
    exact hraw.trans (Nat.mul_le_mul_left 100_000_000_000 hpow)
  have hdepthRaw := binaryFormulaFvSupTrace_cost_le generated.1
  have hgeneratedSquare := Nat.pow_le_pow_left hgeneratedCode 2
  have hdepthProduct := Nat.mul_le_mul
    (Nat.mul_le_mul_left 500 hgeneratedCodeOne) hgeneratedSquare
  have hdepthCost :
      depth.2 <=
        10_000_000_000_000_000_000_000_000 * scale ^ 12 := by
    refine hdepthRaw.trans ?_
    calc
      500 * ((binaryFormulaCode generated.1).length + 1) *
            (binaryFormulaCode generated.1).length ^ 2 <=
          500 * (10_000_001 * scale ^ 4) *
            (10_000_000 * scale ^ 4) ^ 2 :=
        hdepthProduct
      _ =
          (500 * 10_000_001 * 10_000_000 ^ 2) * scale ^ 12 := by
        ring
      _ <=
          10_000_000_000_000_000_000_000_000 * scale ^ 12 := by
        exact Nat.mul_le_mul_right (scale ^ 12) (by norm_num)
  have hdepthSize :
      Nat.size depth.1 <= (binaryFormulaCode generated.1).length := by
    exact binaryFormulaFvSupTrace_size_le_code generated.1
  have hcandidateSize : Nat.size candidateLength <= candidateLength := by
    rw [Nat.size_le]
    exact candidateLength.lt_two_pow_self
  have hcomparisonRaw := binaryNatLeTrace_cost_le depth.1 candidateLength
  have hcomparisonCost :
      comparison.2 <= 30_000_000 * scale ^ 4 := by
    exact hcomparisonRaw.trans (by omega)
  change generated.2 + depth.2 + comparison.2 +
      bodyLength + candidateLength + 5 <=
    100_000_000_000_000_000_000_000_000 * scale ^ 12
  have hbodyTwelve : bodyLength <= scale ^ 12 :=
    (Nat.le_trans (by omega : bodyLength <= scale))
      (by
        have := Nat.pow_le_pow_right hscalePos (show 1 <= 12 by omega)
        simpa using this)
  have hcandidateTwelve : candidateLength <= scale ^ 12 :=
    hcandidateScale.trans (by
      have := Nat.pow_le_pow_right hscalePos (show 1 <= 12 by omega)
      simpa using this)
  have hcomparisonTwelve :
      comparison.2 <= 30_000_000 * scale ^ 12 :=
    hcomparisonCost.trans
      (Nat.mul_le_mul_left 30_000_000
        (Nat.pow_le_pow_right hscalePos (by omega)))
  omega

theorem inductionSentenceGuardTrace_complete
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hequality :
      (PAAxiomCertificate.induction body).sentence = candidate) :
    (inductionSentenceGuardTrace body candidate).1 = true := by
  have hclosure := binaryFormulaCode_emb_univCl_length_ge_fvSup
    (succInd body)
  have htag : 1 <= (binaryNatCode 6).length := by
    have := two_le_binaryNatCode_length 6
    omega
  have hdepth :
      (succInd body).fvSup <=
        (binaryFormulaCode
          (Rewriting.emb (succInd body).univCl :
            LO.FirstOrder.ArithmeticProposition)).length := by
    calc
      (succInd body).fvSup = (succInd body).fvSup * 1 := by simp
      _ <= (succInd body).fvSup * (binaryNatCode 6).length :=
        Nat.mul_le_mul_left _ htag
      _ <= _ := hclosure
  have hcode := congrArg
    (fun sentence : LO.FirstOrder.ArithmeticSentence =>
      (binaryFormulaCode
        (Rewriting.emb sentence :
          LO.FirstOrder.ArithmeticProposition)).length)
    hequality
  apply (inductionSentenceGuardTrace_result_eq_true_iff body candidate).2
  unfold candidateSentenceCodeLength
  exact hdepth.trans_eq (by
    simpa [PAAxiomCertificate.sentence] using hcode)

/-- Formula generated on the accepting branch of the induction guard.  The
free-variable upper bound is first computed by an honest trace, then the same
fixitr and iterated universal closure used by univCl are executed. -/
def tracedInductionClosure
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticProposition :=
  let generated := binarySuccIndTrace body
  let depth := binaryFormulaFvSupTrace generated.1
  let fixed := binaryFormulaFixitrTrace depth.1 generated.1
  let closure := binaryAllClosureTrace fixed.1
  closure.1

theorem tracedInductionClosure_eq
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    tracedInductionClosure body =
      (Rewriting.emb (PAAxiomCertificate.induction body).sentence :
        LO.FirstOrder.ArithmeticProposition) := by
  simp only [tracedInductionClosure]
  rw [binaryAllClosureTrace_result,
    binaryFormulaFixitrTrace_result,
    binaryFormulaFvSupTrace_result,
    binarySuccIndTrace_result]
  simp only [PAAxiomCertificate.sentence]
  rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl']

/-- Guarded induction-sentence comparison.  The potentially long universal
closure is constructed only after its closure depth has been bounded by the
actual candidate formula-code length. -/
def inductionAxiomSentenceEqTrace
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) : Bool × Nat :=
  let guard := inductionSentenceGuardTrace body candidate
  if guard.1 then
    let generated := binarySuccIndTrace body
    let depth := binaryFormulaFvSupTrace generated.1
    let fixed := binaryFormulaFixitrTrace depth.1 generated.1
    let closure := binaryAllClosureTrace fixed.1
    let comparison := formulaEqTrace closure.1
      (Rewriting.emb candidate : LO.FirstOrder.ArithmeticProposition)
    (comparison.1,
      guard.2 + generated.2 + depth.2 + fixed.2 + closure.2 +
        comparison.2 + candidateSentenceCodeLength candidate + 9)
  else
    (false, guard.2 + 1)

theorem inductionAxiomSentenceEqTrace_result_eq_true_iff
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    (inductionAxiomSentenceEqTrace body candidate).1 = true ↔
      (PAAxiomCertificate.induction body).sentence = candidate := by
  by_cases hguard :
      (inductionSentenceGuardTrace body candidate).1 = true
  · simp only [inductionAxiomSentenceEqTrace, hguard, if_pos, Prod.fst]
    rw [formulaEqTrace_result_eq_true_iff]
    change tracedInductionClosure body =
        (Rewriting.emb candidate :
          LO.FirstOrder.ArithmeticProposition) ↔ _
    rw [tracedInductionClosure_eq]
    exact Rewriting.emb_injective.eq_iff
  · have hneq :
        (PAAxiomCertificate.induction body).sentence ≠ candidate := by
      intro hequality
      exact hguard
        (inductionSentenceGuardTrace_complete body candidate hequality)
    simp [inductionAxiomSentenceEqTrace, hguard, hneq]

/-- A single explicit fixed coefficient for the guarded PA-axiom comparison
bounds.  Its second summand is the literal 26-sentence budget above. -/
def guardedAxiomSentenceEqTraceCoefficient : Nat :=
  10 ^ 30 + (3 * constantAxiomSentenceCodeBudget + 4)

set_option maxHeartbeats 600000 in
set_option maxRecDepth 2000 in
theorem inductionAxiomSentenceEqTrace_cost_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    let scale := (binaryFormulaCode body).length +
      candidateSentenceCodeLength candidate + 1
    (inductionAxiomSentenceEqTrace body candidate).2 <=
      guardedAxiomSentenceEqTraceCoefficient * scale ^ 12 := by
  dsimp only
  let guard := inductionSentenceGuardTrace body candidate
  let generated := binarySuccIndTrace body
  let depth := binaryFormulaFvSupTrace generated.1
  let fixed := binaryFormulaFixitrTrace depth.1 generated.1
  let closure := binaryAllClosureTrace fixed.1
  let candidateFormula :=
    (Rewriting.emb candidate : LO.FirstOrder.ArithmeticProposition)
  let comparison := formulaEqTrace closure.1 candidateFormula
  let bodyLength := (binaryFormulaCode body).length
  let candidateLength := candidateSentenceCodeLength candidate
  let generatedLength := (binaryFormulaCode generated.1).length
  let fixedLength := (binaryFormulaCode fixed.1).length
  let closureLength := (binaryFormulaCode closure.1).length
  let scale := bodyLength + candidateLength + 1
  have hscalePos : 0 < scale := by
    dsimp [scale]
    omega
  have hscaleOne : 1 <= scale := hscalePos
  have hbodyScale : bodyLength + 1 <= scale := by
    dsimp [scale]
    omega
  have hcandidateScale : candidateLength <= scale := by
    dsimp [scale]
    omega
  have hpowFourOne : 1 <= scale ^ 4 := by
    simpa using Nat.pow_le_pow_left hscaleOne 4
  have hpowTwelveOne : 1 <= scale ^ 12 := by
    simpa using Nat.pow_le_pow_left hscaleOne 12
  have hscaleFour : scale <= scale ^ 4 := by
    have := Nat.pow_le_pow_right hscalePos (show 1 <= 4 by omega)
    simpa using this
  have hscaleEight : scale <= scale ^ 8 := by
    have := Nat.pow_le_pow_right hscalePos (show 1 <= 8 by omega)
    simpa using this
  have hscaleTwelve : scale <= scale ^ 12 := by
    have := Nat.pow_le_pow_right hscalePos (show 1 <= 12 by omega)
    simpa using this
  have hpowEightTwelve : scale ^ 8 <= scale ^ 12 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hguardCost :
      guard.2 <=
        100_000_000_000_000_000_000_000_000 * scale ^ 12 := by
    simpa [guard, scale, bodyLength, candidateLength] using
      inductionSentenceGuardTrace_cost_le body candidate
  by_cases hguard : guard.1 = true
  · have hguardSemantic :
        (succInd body).fvSup <= candidateLength := by
      have hresult :=
        (inductionSentenceGuardTrace_result_eq_true_iff body candidate).1
          (by simpa only [guard] using hguard)
      simpa only [candidateLength] using hresult
    have hdepthCandidate : depth.1 <= candidateLength := by
      dsimp [depth, generated]
      rw [binaryFormulaFvSupTrace_result, binarySuccIndTrace_result]
      exact hguardSemantic
    have hdepthScale : depth.1 <= scale :=
      hdepthCandidate.trans hcandidateScale
    have hgeneratedCode :
        generatedLength <= 10_000_000 * scale ^ 4 := by
      have hraw := binarySuccIndTrace_code_length_le body
      have hpow := Nat.pow_le_pow_left hbodyScale 4
      exact hraw.trans (by
        simpa only [generatedLength, generated, bodyLength] using
          Nat.mul_le_mul_left 10_000_000 hpow)
    have hgeneratedCodeOne :
        generatedLength + 1 <= 10_000_001 * scale ^ 4 := by
      omega
    have hgeneratedCost :
        generated.2 <= 100_000_000_000 * scale ^ 12 := by
      have hraw := binarySuccIndTrace_cost_le body
      have hpow := Nat.pow_le_pow_left hbodyScale 12
      exact hraw.trans (Nat.mul_le_mul_left 100_000_000_000 hpow)
    have hdepthRaw := binaryFormulaFvSupTrace_cost_le generated.1
    have hgeneratedSquare := Nat.pow_le_pow_left hgeneratedCode 2
    have hdepthProduct := Nat.mul_le_mul
      (Nat.mul_le_mul_left 500 hgeneratedCodeOne) hgeneratedSquare
    have hdepthCost :
        depth.2 <= 10 ^ 25 * scale ^ 12 := by
      refine hdepthRaw.trans ?_
      calc
        500 * (generatedLength + 1) * generatedLength ^ 2 <=
            500 * (10_000_001 * scale ^ 4) *
              (10_000_000 * scale ^ 4) ^ 2 := hdepthProduct
        _ = (500 * 10_000_001 * 10_000_000 ^ 2) *
              scale ^ 12 := by ring
        _ <= 10 ^ 25 * scale ^ 12 :=
          Nat.mul_le_mul_right (scale ^ 12) (by norm_num)
    have hfixitrArgument :
        depth.1 + generatedLength + 1 <=
          10_000_002 * scale ^ 4 := by
      omega
    have hfixitrRaw :=
      binaryFormulaFixitrTrace_cost_le depth.1 generated.1
    have hfixitrSquare := Nat.pow_le_pow_left hfixitrArgument 2
    have hfixedCost : fixed.2 <= 10 ^ 25 * scale ^ 12 := by
      refine hfixitrRaw.trans ?_
      calc
        128 * (depth.1 + generatedLength + 1) ^ 2 * generatedLength <=
            128 * (10_000_002 * scale ^ 4) ^ 2 * generatedLength :=
          Nat.mul_le_mul_right generatedLength
            (Nat.mul_le_mul_left 128 hfixitrSquare)
        _ <=
            128 * (10_000_002 * scale ^ 4) ^ 2 *
              (10_000_000 * scale ^ 4) :=
          Nat.mul_le_mul_left (128 * (10_000_002 * scale ^ 4) ^ 2)
            hgeneratedCode
        _ = (128 * 10_000_002 ^ 2 * 10_000_000) *
              scale ^ 12 := by ring
        _ <= 10 ^ 25 * scale ^ 12 :=
          Nat.mul_le_mul_right (scale ^ 12) (by norm_num)
    have hfixedRaw :=
      binaryFormulaFixitrTrace_code_length_le depth.1 generated.1
    have hfixedSquare := Nat.pow_le_pow_left hgeneratedCodeOne 2
    have hfixedScaled := Nat.mul_le_mul_left 4 hfixedSquare
    have hfixedCode : fixedLength <= 10 ^ 15 * scale ^ 8 := by
      refine hfixedRaw.trans ?_
      calc
        4 * (generatedLength + 1) ^ 2 <=
            4 * (10_000_001 * scale ^ 4) ^ 2 := hfixedScaled
        _ = (4 * 10_000_001 ^ 2) * scale ^ 8 := by ring
        _ <= 10 ^ 15 * scale ^ 8 :=
          Nat.mul_le_mul_right (scale ^ 8) (by norm_num)
    have hclosureRaw : closure.2 <= 24 * (depth.1 + 1) := by
      simpa only [closure, Nat.zero_add] using
        binaryAllClosureTrace_cost_le fixed.1
    have hdepthOne : depth.1 + 1 <= 2 * scale := by
      omega
    have hclosureCost : closure.2 <= 48 * scale ^ 12 := by
      calc
        closure.2 <= 24 * (depth.1 + 1) := hclosureRaw
        _ <= 24 * (2 * scale) := Nat.mul_le_mul_left 24 hdepthOne
        _ = 48 * scale := by omega
        _ <= 48 * scale ^ 12 := Nat.mul_le_mul_left 48 hscaleTwelve
    have htag : (binaryNatCode 6).length <= 10 := by decide
    have hdepthTag :
        depth.1 * (binaryNatCode 6).length <= 10 * scale ^ 8 := by
      have hproduct := Nat.mul_le_mul hdepthCandidate htag
      have hcandidateEight : candidateLength <= scale ^ 8 :=
        hcandidateScale.trans hscaleEight
      have hscaled := Nat.mul_le_mul_right 10 hcandidateEight
      exact hproduct.trans (by simpa [Nat.mul_comm] using hscaled)
    have hclosureCodeEq := binaryAllClosureTrace_code_length_eq fixed.1
    have hclosureCode : closureLength <= 2 * 10 ^ 15 * scale ^ 8 := by
      calc
        closureLength =
            (0 + depth.1) * (binaryNatCode 6).length + fixedLength := by
          simpa only [closureLength, closure, fixedLength] using hclosureCodeEq
        _ <= 2 * 10 ^ 15 * scale ^ 8 := by
          simp only [Nat.zero_add]
          omega
    have hclosureCodeTwelve :
        closureLength <= 2 * 10 ^ 15 * scale ^ 12 :=
      hclosureCode.trans
        (Nat.mul_le_mul_left (2 * 10 ^ 15) hpowEightTwelve)
    have hcandidateTwelve : candidateLength <= scale ^ 12 :=
      hcandidateScale.trans hscaleTwelve
    have hcomparisonRaw := formulaEqTrace_cost_le closure.1 candidateFormula
    have hcandidateCode :
        (binaryFormulaCode candidateFormula).length = candidateLength := by
      rfl
    have hcomparisonCost :
        comparison.2 <= 5 * 10 ^ 15 * scale ^ 12 := by
      exact hcomparisonRaw.trans (by
        rw [hcandidateCode]
        omega)
    have hnine : 9 <= 9 * scale ^ 12 :=
      Nat.mul_le_mul_left 9 hpowTwelveOne
    have hcoefficient :
        100_000_000_000_000_000_000_000_000 +
            100_000_000_000 + 10 ^ 25 + 10 ^ 25 + 48 +
            5 * 10 ^ 15 + 1 + 9 <=
          guardedAxiomSentenceEqTraceCoefficient := by
      have hnumeric :
          100_000_000_000_000_000_000_000_000 +
              100_000_000_000 + 10 ^ 25 + 10 ^ 25 + 48 +
              5 * 10 ^ 15 + 1 + 9 <= 10 ^ 30 := by
        norm_num
      unfold guardedAxiomSentenceEqTraceCoefficient
      omega
    have hcoefficientScaled :=
      Nat.mul_le_mul_right (scale ^ 12) hcoefficient
    have hguardActual :
        (inductionSentenceGuardTrace body candidate).1 = true := by
      simpa only [guard] using hguard
    simp only [inductionAxiomSentenceEqTrace, hguardActual, if_pos]
    change
      guard.2 + generated.2 + depth.2 + fixed.2 + closure.2 +
          comparison.2 + candidateLength + 9 <=
        guardedAxiomSentenceEqTraceCoefficient * scale ^ 12
    omega
  · have hone : 1 <= scale ^ 12 := hpowTwelveOne
    have hcoefficient :
        100_000_000_000_000_000_000_000_000 + 1 <=
          guardedAxiomSentenceEqTraceCoefficient := by
      have hnumeric :
          100_000_000_000_000_000_000_000_000 + 1 <= 10 ^ 30 := by
        norm_num
      unfold guardedAxiomSentenceEqTraceCoefficient
      omega
    have hcoefficientScaled :=
      Nat.mul_le_mul_right (scale ^ 12) hcoefficient
    have hguardActual :
        (inductionSentenceGuardTrace body candidate).1 ≠ true := by
      simpa only [guard] using hguard
    simp [inductionAxiomSentenceEqTrace, hguardActual]
    change guard.2 + 1 <=
      guardedAxiomSentenceEqTraceCoefficient * scale ^ 12
    omega

/-- Unified replacement for the old eager certificate.sentence comparison.
All fixed cases are finite constants; only induction uses the guarded branch. -/
def guardedAxiomSentenceEqTrace
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) : Bool × Nat :=
  match certificate with
  | .induction body => inductionAxiomSentenceEqTrace body candidate
  | _ => fixedAxiomSentenceEqTrace certificate candidate

theorem guardedAxiomSentenceEqTrace_result_eq_true_iff
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    (guardedAxiomSentenceEqTrace certificate candidate).1 = true ↔
      certificate.sentence = candidate := by
  cases certificate <;>
    simp [guardedAxiomSentenceEqTrace,
      fixedAxiomSentenceEqTrace_result_eq_true_iff,
      inductionAxiomSentenceEqTrace_result_eq_true_iff,
      FixedPAAxiomCertificate]

theorem fixedAxiomSentenceEqTrace_cost_le_global
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hfixed : FixedPAAxiomCertificate certificate) :
    (fixedAxiomSentenceEqTrace certificate candidate).2 <=
      guardedAxiomSentenceEqTraceCoefficient *
        ((binaryPAAxiomCertificateCode certificate).length +
          candidateSentenceCodeLength candidate + 1) ^ 12 := by
  let scale := (binaryPAAxiomCertificateCode certificate).length +
    candidateSentenceCodeLength candidate + 1
  have hscalePos : 0 < scale := by
    dsimp [scale]
    omega
  have hscaleOne : 1 <= scale := hscalePos
  have hpowEightTwelve : scale ^ 8 <= scale ^ 12 :=
    Nat.pow_le_pow_right hscalePos (by omega)
  have hscaleTwelve : scale <= scale ^ 12 := by
    have := Nat.pow_le_pow_right hscalePos (show 1 <= 12 by omega)
    simpa using this
  have hcandidate : candidateSentenceCodeLength candidate <= scale := by
    dsimp [scale]
    omega
  have hraw := fixedAxiomSentenceEqTrace_cost_le
    certificate candidate hfixed
  have hcoefficient :
      (3 * constantAxiomSentenceCodeBudget + 4) + 1 <=
        guardedAxiomSentenceEqTraceCoefficient := by
    unfold guardedAxiomSentenceEqTraceCoefficient
    omega
  have hproduct := Nat.mul_le_mul_left
    (3 * constantAxiomSentenceCodeBudget + 4) hpowEightTwelve
  have hcandidateTwelve :
      candidateSentenceCodeLength candidate <= scale ^ 12 :=
    hcandidate.trans hscaleTwelve
  have hcoefficientScaled :=
    Nat.mul_le_mul_right (scale ^ 12) hcoefficient
  rw [Nat.add_mul, one_mul] at hcoefficientScaled
  exact hraw.trans (by
    dsimp [scale] at hproduct hcandidateTwelve hcoefficientScaled ⊢
    omega)

theorem guardedAxiomSentenceEqTrace_cost_le
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    (guardedAxiomSentenceEqTrace certificate candidate).2 <=
      guardedAxiomSentenceEqTraceCoefficient *
        ((binaryPAAxiomCertificateCode certificate).length +
          candidateSentenceCodeLength candidate + 1) ^ 12 := by
  cases certificate with
  | induction body =>
      have hraw := inductionAxiomSentenceEqTrace_cost_le body candidate
      have hbody :
          (binaryFormulaCode body).length <=
            (binaryPAAxiomCertificateCode
              (PAAxiomCertificate.induction body)).length := by
        simp only [binaryPAAxiomCertificateCode, List.length_append]
        omega
      have hscale :
          (binaryFormulaCode body).length +
              candidateSentenceCodeLength candidate + 1 <=
            (binaryPAAxiomCertificateCode
                (PAAxiomCertificate.induction body)).length +
              candidateSentenceCodeLength candidate + 1 := by
        omega
      have hpow := Nat.pow_le_pow_left hscale 12
      have hscaled := Nat.mul_le_mul_left
        guardedAxiomSentenceEqTraceCoefficient hpow
      simp only [guardedAxiomSentenceEqTrace]
      exact hraw.trans hscaled
  | eqRefl | eqSymm | eqTrans | addZero | addAssoc | addComm |
      addEqOfLt | zeroLe | zeroLtOne | oneLeOfZeroLt | addLtAdd |
      mulZero | mulOne | mulAssoc | mulComm | mulLtMul | distr |
      ltIrrefl | ltTrans | ltTri =>
      simp only [guardedAxiomSentenceEqTrace]
      apply fixedAxiomSentenceEqTrace_cost_le_global
      simp [FixedPAAxiomCertificate]
  | eqFuncExt functionSymbol =>
      simp only [guardedAxiomSentenceEqTrace]
      apply fixedAxiomSentenceEqTrace_cost_le_global
      simp [FixedPAAxiomCertificate]
  | eqRelExt relationSymbol =>
      simp only [guardedAxiomSentenceEqTrace]
      apply fixedAxiomSentenceEqTrace_cost_le_global
      simp [FixedPAAxiomCertificate]

/-- Public guarded comparator replacing the impossible eager, certificate-only
sentence generator on unrestricted sparse free-variable indices. -/
def axiomSentenceEqTrace
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) : Bool × Nat :=
  guardedAxiomSentenceEqTrace certificate candidate

theorem axiomSentenceEqTrace_result_eq_true_iff
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    (axiomSentenceEqTrace certificate candidate).1 = true ↔
      certificate.sentence = candidate := by
  simpa only [axiomSentenceEqTrace] using
    guardedAxiomSentenceEqTrace_result_eq_true_iff certificate candidate

theorem axiomSentenceEqTrace_cost_le
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    (axiomSentenceEqTrace certificate candidate).2 <=
      guardedAxiomSentenceEqTraceCoefficient *
        ((binaryPAAxiomCertificateCode certificate).length +
          candidateSentenceCodeLength candidate + 1) ^ 12 := by
  simpa only [axiomSentenceEqTrace] using
    guardedAxiomSentenceEqTrace_cost_le certificate candidate

#print axioms binaryTermBShiftTrace_result
#print axioms binaryTermBShiftTrace_cost_le
#print axioms binarySubstitutionBVarTrace_result
#print axioms binaryTermSubstitutionQpowTrace_result
#print axioms binaryTermSubstitutionQpowTrace_cost_le_factor_mul
#print axioms binaryFormulaSubstitutionQpowTrace_result
#print axioms binaryFormulaSubstitutionQpowTrace_cost_le
#print axioms binaryFormulaSubstitutionOneTrace_result
#print axioms binaryFormulaSubstitutionOneTrace_cost_le
#print axioms binaryFormulaFixitrTrace_result
#print axioms binaryFormulaFixitrTrace_code_length_le
#print axioms binaryFormulaFixitrTrace_cost_le
#print axioms binaryFormulaOpenSubstitutionTrace_result
#print axioms binaryFormulaOpenSubstitutionTrace_code_length_le_of_witness
#print axioms binaryFormulaOpenSubstitutionTrace_cost_le_of_witness
#print axioms binarySuccIndTrace_result
#print axioms binarySuccIndTrace_code_length_le
#print axioms binarySuccIndTrace_cost_le
#print axioms constructedSentenceEqTrace_result_eq_true_iff
#print axioms constructedSentenceEqTrace_cost_le
#print axioms fixedAxiomSentenceEqTrace_result_eq_true_iff
#print axioms fixedAxiomSentenceEqTrace_cost_le_global
#print axioms inductionSentenceGuardTrace_result_eq_true_iff
#print axioms inductionSentenceGuardTrace_cost_le
#print axioms inductionSentenceGuardTrace_complete
#print axioms tracedInductionClosure_eq
#print axioms inductionAxiomSentenceEqTrace_result_eq_true_iff
#print axioms inductionAxiomSentenceEqTrace_cost_le
#print axioms guardedAxiomSentenceEqTrace_result_eq_true_iff
#print axioms guardedAxiomSentenceEqTrace_cost_le
#print axioms axiomSentenceEqTrace_result_eq_true_iff
#print axioms axiomSentenceEqTrace_cost_le

#print axioms binaryFormulaCode_allClosure_length
#print axioms binaryFormulaCode_emb_univCl_length_ge_fvSup
#print axioms sparseInductionCertificateCode_length_le
#print axioms sparseInductionCertificateCode_pow_length_le
#print axioms sparseInduction_succInd_fvSup_ge
#print axioms sparseInductionSentenceCode_length_ge
#print axioms sparseInductionSentenceCode_pow_length_ge

end FoundationCompactSyntaxTransformationTrace
