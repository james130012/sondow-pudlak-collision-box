import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Honest execution traces for the core syntax transformations

The formula traces below do not replace rewriting below a quantifier by the
extensionally equal base rewriting.  Instead they build `Rew.qpow` one layer
at a time through `binaryTermQTrace`, and charge every recursive rewriting,
bounded-variable shift, finite-vector traversal, and syntax constructor.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxTransformationTraceCore

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactVerifierFormulaListChecks

abbrev SyntaxTrace (alpha : Type*) := alpha × Nat

/-! ## Term traces -/

def binaryTermFunctionHeaderCost {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ arity) : Nat :=
  (binaryNatCode 2).length + (binaryNatCode arity).length +
    (binaryNatCode (Encodable.encode functionSymbol)).length

def binaryTermBShiftTrace {arity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat arity →
      SyntaxTrace (LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
  | term@(#index) =>
      let result := (#index.succ :
        LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      (result, (binaryTermCode term).length +
        (binaryTermCode result).length + 3)
  | term@(&index) =>
      let result := (&index :
        LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      (result, (binaryTermCode term).length +
        (binaryTermCode result).length + 3)
  | Semiterm.func functionSymbol arguments =>
      let traces := fun index =>
        binaryTermBShiftTrace (arguments index)
      (Semiterm.func functionSymbol (fun index => (traces index).1),
        2 * binaryTermFunctionHeaderCost functionSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))

def binaryTermShiftTrace {arity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat arity →
      SyntaxTrace (LO.FirstOrder.ArithmeticSemiterm Nat arity)
  | term@(#index) =>
      let result := (#index :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)
      (result, (binaryTermCode term).length +
        (binaryTermCode result).length + 3)
  | term@(&index) =>
      let result := (&(index + 1) :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)
      (result, (binaryTermCode term).length +
        (binaryTermCode result).length + 3)
  | Semiterm.func functionSymbol arguments =>
      let traces := fun index => binaryTermShiftTrace (arguments index)
      (Semiterm.func functionSymbol (fun index => (traces index).1),
        2 * binaryTermFunctionHeaderCost functionSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))

def binaryTermFreeTrace {arity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1) →
      SyntaxTrace (LO.FirstOrder.ArithmeticSemiterm Nat arity)
  | term@(#index) =>
      Fin.lastCases
        (let result := (&0 :
          LO.FirstOrder.ArithmeticSemiterm Nat arity)
         (result, (binaryTermCode term).length +
           (binaryTermCode result).length + 3))
        (fun previous =>
          let result := (#previous :
            LO.FirstOrder.ArithmeticSemiterm Nat arity)
          (result, (binaryTermCode term).length +
            (binaryTermCode result).length + 3)) index
  | term@(&index) =>
      let result := (&(index + 1) :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)
      (result, (binaryTermCode term).length +
        (binaryTermCode result).length + 3)
  | Semiterm.func functionSymbol arguments =>
      let traces := fun index => binaryTermFreeTrace (arguments index)
      (Semiterm.func functionSymbol (fun index => (traces index).1),
        2 * binaryTermFunctionHeaderCost functionSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))

theorem binaryTermBShiftTrace_result {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermBShiftTrace term).1 = Rew.bShift term := by
  induction term with
  | bvar index => rfl
  | fvar index => rfl
  | func functionSymbol arguments ih =>
      simp only [binaryTermBShiftTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermShiftTrace_result {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermShiftTrace term).1 = Rew.shift term := by
  induction term with
  | bvar index => rfl
  | fvar index => rfl
  | func functionSymbol arguments ih =>
      simp only [binaryTermShiftTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermFreeTrace_result {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1)) :
    (binaryTermFreeTrace term).1 = Rew.free term := by
  induction term with
  | bvar index =>
      cases index using Fin.lastCases <;>
        simp [binaryTermFreeTrace]
  | fvar index =>
      simp [binaryTermFreeTrace]
  | func functionSymbol arguments ih =>
      simp only [binaryTermFreeTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermBShiftTrace_cost_le {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermBShiftTrace term).2 ≤
      16 * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      have hinput := four_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have houtput :=
        binaryTermCode_bShift_length_le_add_symbols
          (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have hsymbols := termSymbolCount_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have htraceOutput :
          (binaryTermCode
            (binaryTermBShiftTrace
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length ≤
            3 * (binaryTermCode
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length := by
        rw [binaryTermBShiftTrace_result]
        omega
      have hcostEq :
          (binaryTermBShiftTrace
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).2 =
            (binaryTermCode
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length +
            (binaryTermCode
              (binaryTermBShiftTrace
                (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length +
            3 := by rfl
      rw [hcostEq]
      omega
  | fvar index =>
      have hinput := four_le_binaryTermCode_length
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have houtput :=
        binaryTermCode_bShift_length_le_add_symbols
          (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have hsymbols := termSymbolCount_le_binaryTermCode_length
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have htraceOutput :
          (binaryTermCode
            (binaryTermBShiftTrace
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length ≤
            3 * (binaryTermCode
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length := by
        rw [binaryTermBShiftTrace_result]
        omega
      have hcostEq :
          (binaryTermBShiftTrace
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).2 =
            (binaryTermCode
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length +
            (binaryTermCode
              (binaryTermBShiftTrace
                (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length +
            3 := by rfl
      rw [hcostEq]
      omega
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermBShiftTrace (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                16 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hheader : 1 ≤ binaryTermFunctionHeaderCost functionSymbol := by
        have htag := two_le_binaryNatCode_length 2
        dsimp [binaryTermFunctionHeaderCost]
        omega
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermBShiftTrace (arguments index)).2) ≤
            16 * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                16 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      simp only [binaryTermBShiftTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn]
      dsimp [binaryTermFunctionHeaderCost] at hheader ⊢
      omega

theorem binaryTermShiftTrace_cost_le {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermShiftTrace term).2 ≤
      16 * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      have hinput := four_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have houtput := binaryTermCode_shift_length_le
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have htraceOutput :
          (binaryTermCode
            (binaryTermShiftTrace
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length ≤
            2 * (binaryTermCode
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length := by
        rw [binaryTermShiftTrace_result]
        exact houtput
      have hcostEq :
          (binaryTermShiftTrace
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).2 =
            (binaryTermCode
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length +
            (binaryTermCode
              (binaryTermShiftTrace
                (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length +
            3 := by rfl
      rw [hcostEq]
      omega
  | fvar index =>
      have hinput := four_le_binaryTermCode_length
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have houtput := binaryTermCode_shift_length_le
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have htraceOutput :
          (binaryTermCode
            (binaryTermShiftTrace
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length ≤
            2 * (binaryTermCode
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length := by
        rw [binaryTermShiftTrace_result]
        exact houtput
      have hcostEq :
          (binaryTermShiftTrace
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).2 =
            (binaryTermCode
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length +
            (binaryTermCode
              (binaryTermShiftTrace
                (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).1).length +
            3 := by rfl
      rw [hcostEq]
      omega
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermShiftTrace (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                16 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hheader : 1 ≤ binaryTermFunctionHeaderCost functionSymbol := by
        have htag := two_le_binaryNatCode_length 2
        dsimp [binaryTermFunctionHeaderCost]
        omega
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermShiftTrace (arguments index)).2) ≤
            16 * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                16 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      simp only [binaryTermShiftTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn]
      dsimp [binaryTermFunctionHeaderCost] at hheader ⊢
      omega

theorem binaryTermFreeTrace_cost_le {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1)) :
    (binaryTermFreeTrace term).2 ≤
      16 * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      have hinput := four_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      have houtput := binaryTermCode_free_length_le
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      have htraceOutput :
          (binaryTermCode
            (binaryTermFreeTrace
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat
                (arity + 1))).1).length ≤
            2 * (binaryTermCode
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat
                (arity + 1))).length := by
        rw [binaryTermFreeTrace_result]
        exact houtput
      have hcostEq :
          (binaryTermFreeTrace
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat
              (arity + 1))).2 =
            (binaryTermCode
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat
                (arity + 1))).length +
            (binaryTermCode
              (binaryTermFreeTrace
                (#index : LO.FirstOrder.ArithmeticSemiterm Nat
                  (arity + 1))).1).length + 3 := by
        cases index using Fin.lastCases <;>
          simp [binaryTermFreeTrace]
      rw [hcostEq]
      omega
  | fvar index =>
      have hinput := four_le_binaryTermCode_length
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      have houtput := binaryTermCode_free_length_le
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1))
      have htraceOutput :
          (binaryTermCode
            (binaryTermFreeTrace
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                (arity + 1))).1).length ≤
            2 * (binaryTermCode
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                (arity + 1))).length := by
        rw [binaryTermFreeTrace_result]
        exact houtput
      have hcostEq :
          (binaryTermFreeTrace
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat
              (arity + 1))).2 =
            (binaryTermCode
              (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                (arity + 1))).length +
            (binaryTermCode
              (binaryTermFreeTrace
                (&index : LO.FirstOrder.ArithmeticSemiterm Nat
                  (arity + 1))).1).length + 3 := by rfl
      rw [hcostEq]
      omega
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFreeTrace (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                16 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hheader : 1 ≤ binaryTermFunctionHeaderCost functionSymbol := by
        have htag := two_le_binaryNatCode_length 2
        dsimp [binaryTermFunctionHeaderCost]
        omega
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermFreeTrace (arguments index)).2) ≤
            16 * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                16 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      simp only [binaryTermFreeTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn]
      dsimp [binaryTermFunctionHeaderCost] at hheader ⊢
      omega

/-!
`binaryTermQTrace previous` is the operational lift of a previously costed
rewriting through one quantifier.  In the successor-bound-variable and free
variable cases it really invokes `previous` and then the recursive bounded
shift trace; this is the work hidden by an extensional `q_shift`/`q_free`
rewrite.
-/
def binaryTermQTrace {sourceArity targetArity : Nat}
    (previous : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity →
      SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat targetArity)) :
    LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1) →
      SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1))
  | #index =>
      Fin.cases
        (let input := (#0 :
          LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1))
         let output := (#0 :
          LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1))
         (output, (binaryTermCode input).length +
           (binaryTermCode output).length + 3))
        (fun previousIndex =>
        let rewritten := previous (#previousIndex)
        let lifted := binaryTermBShiftTrace rewritten.1
        let input := (#previousIndex.succ :
          LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1))
        (lifted.1, rewritten.2 + lifted.2 +
          (binaryTermCode input).length +
          (binaryTermCode lifted.1).length + 3)) index
  | &index =>
      let rewritten := previous (&index)
      let lifted := binaryTermBShiftTrace rewritten.1
      let input := (&index :
        LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1))
      (lifted.1, rewritten.2 + lifted.2 +
        (binaryTermCode input).length +
        (binaryTermCode lifted.1).length + 3)
  | Semiterm.func functionSymbol arguments =>
      let traces := fun index => binaryTermQTrace previous (arguments index)
      (Semiterm.func functionSymbol (fun index => (traces index).1),
        2 * binaryTermFunctionHeaderCost functionSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))

theorem binaryTermQTrace_result
    {sourceArity targetArity : Nat}
    (previous : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity →
      SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat targetArity))
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (hprevious : ∀ term, (previous term).1 = rewriting term)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1)) :
    (binaryTermQTrace previous term).1 = rewriting.q term := by
  induction term with
  | bvar index =>
      cases index using Fin.cases with
      | zero => simp [binaryTermQTrace]
      | succ index =>
          simp [binaryTermQTrace, hprevious,
            binaryTermBShiftTrace_result]
  | fvar index =>
      simp [binaryTermQTrace, hprevious,
        binaryTermBShiftTrace_result]
  | func functionSymbol arguments ih =>
      simp only [binaryTermQTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermQTrace_cost_le
    {sourceArity targetArity factor : Nat}
    (previous : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity →
      SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat targetArity))
    (hpreviousCost : ∀ term,
      (previous term).2 ≤ factor * (binaryTermCode term).length)
    (hpreviousCode : ∀ term,
      (binaryTermCode (previous term).1).length ≤
        2 * (binaryTermCode term).length)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1)) :
    (binaryTermQTrace previous term).2 ≤
      (factor + 50) * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      cases index using Fin.cases with
      | zero =>
          let input := (#0 : LO.FirstOrder.ArithmeticSemiterm Nat
            (sourceArity + 1))
          have hinput := four_le_binaryTermCode_length input
          have hcostEq :
              (binaryTermQTrace previous input).2 =
                (binaryTermCode input).length +
                (binaryTermCode input).length + 3 := by
            rfl
          have hfactor : 50 ≤ factor + 50 := by omega
          rw [hcostEq]
          calc
            (binaryTermCode input).length +
                (binaryTermCode input).length + 3 ≤
              3 * (binaryTermCode input).length := by omega
            _ ≤ (factor + 50) * (binaryTermCode input).length :=
              Nat.mul_le_mul_right (binaryTermCode input).length
                (by omega)
      | succ index =>
          let old :=
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity)
          let current :=
            (#index.succ : LO.FirstOrder.ArithmeticSemiterm Nat
              (sourceArity + 1))
          let rewritten := previous old
          have hinput :
              (binaryTermCode old).length ≤
                (binaryTermCode current).length := by
            dsimp [old, current]
            simpa [binaryTermCode] using
              FoundationCompactCanonicalDecodeLength.binaryNatCode_length_mono
                (Nat.le_succ index.val)
          have hcostOld := hpreviousCost old
          have hcost := hcostOld.trans
            (Nat.mul_le_mul_left factor hinput)
          have hrewritten := hpreviousCode old
          have hrewrittenCurrent :
              (binaryTermCode rewritten.1).length ≤
                2 * (binaryTermCode current).length := by
            exact hrewritten.trans
              (Nat.mul_le_mul_left 2 hinput)
          have hlift := binaryTermBShiftTrace_cost_le rewritten.1
          have hliftCurrent :
              (binaryTermBShiftTrace rewritten.1).2 ≤
                32 * (binaryTermCode current).length := by
            calc
              _ ≤ 16 * (2 * (binaryTermCode current).length) :=
                hlift.trans
                  (Nat.mul_le_mul_left 16 hrewrittenCurrent)
              _ = 32 * (binaryTermCode current).length := by omega
          have hliftCodeRaw :=
            binaryTermCode_bShift_length_le_add_symbols rewritten.1
          have hsymbols :=
            termSymbolCount_le_binaryTermCode_length rewritten.1
          have hliftCode :
              (binaryTermCode
                (binaryTermBShiftTrace rewritten.1).1).length ≤
                6 * (binaryTermCode current).length := by
            rw [binaryTermBShiftTrace_result]
            omega
          have hcurrent := four_le_binaryTermCode_length current
          simp only [binaryTermQTrace]
          dsimp [old, current, rewritten] at *
          rw [Nat.add_mul]
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
            (binaryTermCode current).length := by
        rfl
      have hcostOld := hpreviousCost old
      have hcost :
          rewritten.2 ≤
            factor * (binaryTermCode current).length := by
        simpa [rewritten, hsame] using hcostOld
      have hrewritten := hpreviousCode old
      have hrewrittenCurrent :
          (binaryTermCode rewritten.1).length ≤
            2 * (binaryTermCode current).length := by
        simpa [rewritten, hsame] using hrewritten
      have hlift := binaryTermBShiftTrace_cost_le rewritten.1
      have hliftCurrent :
          (binaryTermBShiftTrace rewritten.1).2 ≤
            32 * (binaryTermCode current).length := by
        calc
          _ ≤ 16 * (2 * (binaryTermCode current).length) :=
            hlift.trans
              (Nat.mul_le_mul_left 16 hrewrittenCurrent)
          _ = 32 * (binaryTermCode current).length := by omega
      have hliftCodeRaw :=
        binaryTermCode_bShift_length_le_add_symbols rewritten.1
      have hsymbols :=
        termSymbolCount_le_binaryTermCode_length rewritten.1
      have hliftCode :
          (binaryTermCode
            (binaryTermBShiftTrace rewritten.1).1).length ≤
            6 * (binaryTermCode current).length := by
        rw [binaryTermBShiftTrace_result]
        omega
      have hinput := four_le_binaryTermCode_length current
      simp only [binaryTermQTrace]
      dsimp [old, current, rewritten] at *
      rw [Nat.add_mul]
      omega
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermQTrace previous (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                (factor + 50) *
                  (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermQTrace previous (arguments index)).2) ≤
            (factor + 50) * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                (factor + 50) *
                  (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader : 1 ≤ binaryTermFunctionHeaderCost functionSymbol := by
        have htag := two_le_binaryNatCode_length 2
        dsimp [binaryTermFunctionHeaderCost]
        omega
      have hfactor : 5 ≤ factor + 50 := by omega
      have hscaled := Nat.mul_le_mul_right
        (binaryTermFunctionHeaderCost functionSymbol) hfactor
      have hcharge :
          2 * binaryTermFunctionHeaderCost functionSymbol + 3 ≤
            (factor + 50) *
              binaryTermFunctionHeaderCost functionSymbol := by
        omega
      simp only [binaryTermQTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [binaryTermFunctionHeaderCost] at hheader hcharge ⊢
      omega

def binaryTermShiftQpowTrace :
    (depth : Nat) →
      LO.FirstOrder.ArithmeticSemiterm Nat depth →
        SyntaxTrace (LO.FirstOrder.ArithmeticSemiterm Nat depth)
  | 0 => binaryTermShiftTrace
  | depth + 1 => binaryTermQTrace (binaryTermShiftQpowTrace depth)

def binaryTermFreeQpowTrace :
    (depth : Nat) →
      LO.FirstOrder.ArithmeticSemiterm Nat (depth + 1) →
        SyntaxTrace (LO.FirstOrder.ArithmeticSemiterm Nat depth)
  | 0 => binaryTermFreeTrace
  | depth + 1 => binaryTermQTrace (binaryTermFreeQpowTrace depth)

theorem binaryTermShiftQpowTrace_result :
    ∀ (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat depth),
      (binaryTermShiftQpowTrace depth term).1 =
        (Rew.shift (L := ℒₒᵣ) (n := depth)) term
  | 0, term => by
      simpa [binaryTermShiftQpowTrace] using
        binaryTermShiftTrace_result term
  | depth + 1, term => by
      simpa [binaryTermShiftQpowTrace, Rew.q_shift] using
        binaryTermQTrace_result
          (binaryTermShiftQpowTrace depth)
          (Rew.shift (L := ℒₒᵣ) (n := depth))
          (binaryTermShiftQpowTrace_result depth) term

theorem binaryTermFreeQpowTrace_result :
    ∀ (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat (depth + 1)),
      (binaryTermFreeQpowTrace depth term).1 =
        (Rew.free (L := ℒₒᵣ) (n := depth)) term
  | 0, term => by
      simpa [binaryTermFreeQpowTrace] using
        binaryTermFreeTrace_result term
  | depth + 1, term => by
      simpa [binaryTermFreeQpowTrace, Rew.q_free] using
        binaryTermQTrace_result
          (binaryTermFreeQpowTrace depth)
          (Rew.free (L := ℒₒᵣ) (n := depth))
          (binaryTermFreeQpowTrace_result depth) term

theorem binaryTermShiftQpowTrace_code_length_le
    (depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat depth) :
    (binaryTermCode (binaryTermShiftQpowTrace depth term).1).length ≤
      2 * (binaryTermCode term).length := by
  rw [binaryTermShiftQpowTrace_result]
  exact binaryTermCode_shift_length_le term

theorem binaryTermFreeQpowTrace_code_length_le
    (depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (depth + 1)) :
    (binaryTermCode (binaryTermFreeQpowTrace depth term).1).length ≤
      2 * (binaryTermCode term).length := by
  rw [binaryTermFreeQpowTrace_result]
  exact binaryTermCode_free_length_le term

theorem binaryTermShiftQpowTrace_cost_le :
    ∀ (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat depth),
      (binaryTermShiftQpowTrace depth term).2 ≤
        (16 + 50 * depth) * (binaryTermCode term).length
  | 0, term => by
      simpa [binaryTermShiftQpowTrace] using
        binaryTermShiftTrace_cost_le term
  | depth + 1, term => by
      have h := binaryTermQTrace_cost_le
        (binaryTermShiftQpowTrace depth)
        (binaryTermShiftQpowTrace_cost_le depth)
        (binaryTermShiftQpowTrace_code_length_le depth) term
      have hfactor :
          (16 + 50 * depth) + 50 = 16 + 50 * (depth + 1) := by
        omega
      simpa only [binaryTermShiftQpowTrace, hfactor] using h

theorem binaryTermFreeQpowTrace_cost_le :
    ∀ (depth : Nat)
      (term : LO.FirstOrder.ArithmeticSemiterm Nat (depth + 1)),
      (binaryTermFreeQpowTrace depth term).2 ≤
        (16 + 50 * depth) * (binaryTermCode term).length
  | 0, term => by
      simpa [binaryTermFreeQpowTrace] using
        binaryTermFreeTrace_cost_le term
  | depth + 1, term => by
      have h := binaryTermQTrace_cost_le
        (binaryTermFreeQpowTrace depth)
        (binaryTermFreeQpowTrace_cost_le depth)
        (binaryTermFreeQpowTrace_code_length_le depth) term
      have hfactor :
          (16 + 50 * depth) + 50 = 16 + 50 * (depth + 1) := by
        omega
      simpa only [binaryTermFreeQpowTrace, hfactor] using h

/-! ## Formula traces with explicit quantifier depth -/

def binaryFormulaAtomHeaderCost (tag : Nat) {arity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ arity) : Nat :=
  (binaryNatCode tag).length + (binaryNatCode arity).length +
    (binaryNatCode (Encodable.encode relationSymbol)).length

def binaryFormulaNodeHeaderCost (tag : Nat) : Nat :=
  (binaryNatCode tag).length

def binaryFormulaRewTrace {sourceArity targetArity : Nat}
    (previous : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity →
      SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat targetArity)) :
    LO.FirstOrder.ArithmeticSemiformula Nat sourceArity →
      SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiformula Nat targetArity)
  | ⊤ => (⊤, 2 * binaryFormulaNodeHeaderCost 2 + 3)
  | ⊥ => (⊥, 2 * binaryFormulaNodeHeaderCost 3 + 3)
  | Semiformula.rel relationSymbol arguments =>
      let traces := fun index => previous (arguments index)
      (Semiformula.rel relationSymbol
        (fun index => (traces index).1),
        2 * binaryFormulaAtomHeaderCost 0 relationSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))
  | Semiformula.nrel relationSymbol arguments =>
      let traces := fun index => previous (arguments index)
      (Semiformula.nrel relationSymbol
        (fun index => (traces index).1),
        2 * binaryFormulaAtomHeaderCost 1 relationSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))
  | φ ⋏ ψ =>
      let left := binaryFormulaRewTrace previous φ
      let right := binaryFormulaRewTrace previous ψ
      (left.1 ⋏ right.1,
        left.2 + right.2 + 2 * binaryFormulaNodeHeaderCost 4 + 3)
  | φ ⋎ ψ =>
      let left := binaryFormulaRewTrace previous φ
      let right := binaryFormulaRewTrace previous ψ
      (left.1 ⋎ right.1,
        left.2 + right.2 + 2 * binaryFormulaNodeHeaderCost 5 + 3)
  | ∀⁰ φ =>
      let body := binaryFormulaRewTrace
        (binaryTermQTrace previous) φ
      (∀⁰ body.1, body.2 + 2 * binaryFormulaNodeHeaderCost 6 + 3)
  | ∃⁰ φ =>
      let body := binaryFormulaRewTrace
        (binaryTermQTrace previous) φ
      (∃⁰ body.1, body.2 + 2 * binaryFormulaNodeHeaderCost 7 + 3)

theorem binaryFormulaRewTrace_result
    {sourceArity targetArity : Nat}
    (previous : LO.FirstOrder.ArithmeticSemiterm Nat sourceArity →
      SyntaxTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat targetArity))
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (hprevious : ∀ term, (previous term).1 = rewriting term) :
    ∀ formula :
        LO.FirstOrder.ArithmeticSemiformula Nat sourceArity,
      (binaryFormulaRewTrace previous formula).1 =
        Rewriting.app rewriting formula
  | ⊤ => rfl
  | ⊥ => rfl
  | Semiformula.rel relationSymbol arguments => by
      simp only [binaryFormulaRewTrace, Semiformula.rew_rel]
      congr
      funext index
      exact hprevious (arguments index)
  | Semiformula.nrel relationSymbol arguments => by
      simp only [binaryFormulaRewTrace, Semiformula.rew_nrel]
      congr
      funext index
      exact hprevious (arguments index)
  | left ⋏ right => by
      simp only [binaryFormulaRewTrace,
        LogicalConnective.HomClass.map_and]
      rw [binaryFormulaRewTrace_result previous rewriting hprevious left,
        binaryFormulaRewTrace_result previous rewriting hprevious right]
  | left ⋎ right => by
      simp only [binaryFormulaRewTrace,
        LogicalConnective.HomClass.map_or]
      rw [binaryFormulaRewTrace_result previous rewriting hprevious left,
        binaryFormulaRewTrace_result previous rewriting hprevious right]
  | ∀⁰ body => by
      have hq : ∀ term,
          (binaryTermQTrace previous term).1 = rewriting.q term :=
        fun term =>
          binaryTermQTrace_result previous rewriting hprevious term
      simp only [binaryFormulaRewTrace, Rewriting.app_all]
      rw [binaryFormulaRewTrace_result
        (binaryTermQTrace previous) rewriting.q hq body]
  | ∃⁰ body => by
      have hq : ∀ term,
          (binaryTermQTrace previous term).1 = rewriting.q term :=
        fun term =>
          binaryTermQTrace_result previous rewriting hprevious term
      simp only [binaryFormulaRewTrace, Rewriting.app_exs]
      rw [binaryFormulaRewTrace_result
        (binaryTermQTrace previous) rewriting.q hq body]

def binaryFormulaShiftQpowTrace :
    (depth : Nat) →
      LO.FirstOrder.ArithmeticSemiformula Nat depth →
        SyntaxTrace
          (LO.FirstOrder.ArithmeticSemiformula Nat depth)
  | _, ⊤ => (⊤, 2 * binaryFormulaNodeHeaderCost 2 + 3)
  | _, ⊥ => (⊥, 2 * binaryFormulaNodeHeaderCost 3 + 3)
  | depth, Semiformula.rel relationSymbol arguments =>
      let traces := fun index =>
        binaryTermShiftQpowTrace depth (arguments index)
      (Semiformula.rel relationSymbol
        (fun index => (traces index).1),
        2 * binaryFormulaAtomHeaderCost 0 relationSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))
  | depth, Semiformula.nrel relationSymbol arguments =>
      let traces := fun index =>
        binaryTermShiftQpowTrace depth (arguments index)
      (Semiformula.nrel relationSymbol
        (fun index => (traces index).1),
        2 * binaryFormulaAtomHeaderCost 1 relationSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))
  | depth, φ ⋏ ψ =>
      let left := binaryFormulaShiftQpowTrace depth φ
      let right := binaryFormulaShiftQpowTrace depth ψ
      (left.1 ⋏ right.1,
        left.2 + right.2 + 2 * binaryFormulaNodeHeaderCost 4 + 3)
  | depth, φ ⋎ ψ =>
      let left := binaryFormulaShiftQpowTrace depth φ
      let right := binaryFormulaShiftQpowTrace depth ψ
      (left.1 ⋎ right.1,
        left.2 + right.2 + 2 * binaryFormulaNodeHeaderCost 5 + 3)
  | depth, ∀⁰ φ =>
      let body := binaryFormulaShiftQpowTrace (depth + 1) φ
      (∀⁰ body.1, body.2 + 2 * binaryFormulaNodeHeaderCost 6 + 3)
  | depth, ∃⁰ φ =>
      let body := binaryFormulaShiftQpowTrace (depth + 1) φ
      (∃⁰ body.1, body.2 + 2 * binaryFormulaNodeHeaderCost 7 + 3)

def binaryFormulaFreeQpowTrace (depth : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (depth + 1)) :
    SyntaxTrace (LO.FirstOrder.ArithmeticSemiformula Nat depth) :=
  binaryFormulaRewTrace (binaryTermFreeQpowTrace depth) formula

theorem binaryFormulaShiftQpowTrace_result :
    ∀ (depth : Nat)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat depth),
      (binaryFormulaShiftQpowTrace depth formula).1 =
        Rewriting.shift formula
  | _, ⊤ => rfl
  | _, ⊥ => rfl
  | depth, Semiformula.rel relationSymbol arguments => by
      simp only [binaryFormulaShiftQpowTrace, Semiformula.rew_rel]
      congr
      funext index
      exact binaryTermShiftQpowTrace_result depth (arguments index)
  | depth, Semiformula.nrel relationSymbol arguments => by
      simp only [binaryFormulaShiftQpowTrace, Semiformula.rew_nrel]
      congr
      funext index
      exact binaryTermShiftQpowTrace_result depth (arguments index)
  | depth, φ ⋏ ψ => by
      simp only [binaryFormulaShiftQpowTrace,
        LogicalConnective.HomClass.map_and]
      rw [binaryFormulaShiftQpowTrace_result depth φ,
        binaryFormulaShiftQpowTrace_result depth ψ]
  | depth, φ ⋎ ψ => by
      simp only [binaryFormulaShiftQpowTrace,
        LogicalConnective.HomClass.map_or]
      rw [binaryFormulaShiftQpowTrace_result depth φ,
        binaryFormulaShiftQpowTrace_result depth ψ]
  | depth, ∀⁰ φ => by
      simp only [binaryFormulaShiftQpowTrace, Rewriting.app_all,
        Rew.q_shift]
      simpa using
        binaryFormulaShiftQpowTrace_result (depth + 1) φ
  | depth, ∃⁰ φ => by
      simp only [binaryFormulaShiftQpowTrace, Rewriting.app_exs,
        Rew.q_shift]
      simpa using
        binaryFormulaShiftQpowTrace_result (depth + 1) φ

theorem binaryFormulaFreeQpowTrace_result :
    ∀ (depth : Nat)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat (depth + 1)),
      (binaryFormulaFreeQpowTrace depth formula).1 =
        Rewriting.free formula
  | _, ⊤ => rfl
  | _, ⊥ => rfl
  | depth, Semiformula.rel relationSymbol arguments => by
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        Semiformula.rew_rel]
      congr
      funext index
      exact binaryTermFreeQpowTrace_result depth (arguments index)
  | depth, Semiformula.nrel relationSymbol arguments => by
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        Semiformula.rew_nrel]
      congr
      funext index
      exact binaryTermFreeQpowTrace_result depth (arguments index)
  | depth, φ ⋏ ψ => by
      have hφ :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) φ).1 =
            Rewriting.free φ := by
        simpa only [binaryFormulaFreeQpowTrace] using
          binaryFormulaFreeQpowTrace_result depth φ
      have hψ :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) ψ).1 =
            Rewriting.free ψ := by
        simpa only [binaryFormulaFreeQpowTrace] using
          binaryFormulaFreeQpowTrace_result depth ψ
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        LogicalConnective.HomClass.map_and]
      rw [hφ, hψ]
  | depth, φ ⋎ ψ => by
      have hφ :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) φ).1 =
            Rewriting.free φ := by
        simpa only [binaryFormulaFreeQpowTrace] using
          binaryFormulaFreeQpowTrace_result depth φ
      have hψ :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) ψ).1 =
            Rewriting.free ψ := by
        simpa only [binaryFormulaFreeQpowTrace] using
          binaryFormulaFreeQpowTrace_result depth ψ
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        LogicalConnective.HomClass.map_or]
      rw [hφ, hψ]
  | depth, ∀⁰ φ => by
      have hq :
          binaryTermQTrace (binaryTermFreeQpowTrace depth) =
            binaryTermFreeQpowTrace (depth + 1) := by
        funext term
        rfl
      have hφ :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace (depth + 1)) φ).1 =
            Rewriting.free φ := by
        simpa only [binaryFormulaFreeQpowTrace] using
          binaryFormulaFreeQpowTrace_result (depth + 1) φ
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        Rewriting.app_all,
        Rew.q_free]
      rw [hq, hφ]
  | depth, ∃⁰ φ => by
      have hq :
          binaryTermQTrace (binaryTermFreeQpowTrace depth) =
            binaryTermFreeQpowTrace (depth + 1) := by
        funext term
        rfl
      have hφ :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace (depth + 1)) φ).1 =
            Rewriting.free φ := by
        simpa only [binaryFormulaFreeQpowTrace] using
          binaryFormulaFreeQpowTrace_result (depth + 1) φ
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        Rewriting.app_exs,
        Rew.q_free]
      rw [hq, hφ]

def binaryFormulaShiftTrace
    (formula : LO.FirstOrder.ArithmeticProposition) :
    SyntaxTrace LO.FirstOrder.ArithmeticProposition :=
  binaryFormulaShiftQpowTrace 0 formula

def binaryFormulaFreeTrace
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    SyntaxTrace LO.FirstOrder.ArithmeticProposition :=
  binaryFormulaFreeQpowTrace 0 formula

theorem binaryFormulaShiftTrace_result
    (formula : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaShiftTrace formula).1 = Rewriting.shift formula := by
  simpa [binaryFormulaShiftTrace] using
    binaryFormulaShiftQpowTrace_result 0 formula

theorem binaryFormulaFreeTrace_result
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaFreeTrace formula).1 = Rewriting.free formula := by
  simpa [binaryFormulaFreeTrace] using
    binaryFormulaFreeQpowTrace_result 0 formula

theorem binaryFormulaHeaderCharge_le
    (header budget : Nat) (hheader : 1 ≤ header) :
    2 * header + 3 ≤ 100 * (budget + 1) * header := by
  have hfactor : 5 ≤ 100 * (budget + 1) := by omega
  have hscaled := Nat.mul_le_mul_right header hfactor
  omega

theorem binaryFormulaShiftQpowTrace_cost_le :
    ∀ (depth : Nat)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat depth)
      (budget : Nat),
      depth + formulaSymbolCount formula ≤ budget →
      (binaryFormulaShiftQpowTrace depth formula).2 ≤
        (100 * (budget + 1)) *
          (binaryFormulaCode formula).length
  | _, ⊤, budget, hbudget => by
      change
        2 * binaryFormulaNodeHeaderCost 2 + 3 ≤
          100 * (budget + 1) * binaryFormulaNodeHeaderCost 2
      apply binaryFormulaHeaderCharge_le
      have htag := two_le_binaryNatCode_length 2
      dsimp [binaryFormulaNodeHeaderCost]
      omega
  | _, ⊥, budget, hbudget => by
      change
        2 * binaryFormulaNodeHeaderCost 3 + 3 ≤
          100 * (budget + 1) * binaryFormulaNodeHeaderCost 3
      apply binaryFormulaHeaderCharge_le
      have htag := two_le_binaryNatCode_length 3
      dsimp [binaryFormulaNodeHeaderCost]
      omega
  | depth, Semiformula.rel relationSymbol arguments, budget, hbudget => by
      have hdepth : 16 + 50 * depth ≤ 100 * (budget + 1) := by
        have : depth ≤ budget := by
          have hone := one_le_formulaSymbolCount
            (Semiformula.rel relationSymbol arguments)
          omega
        omega
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermShiftQpowTrace depth
                  (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (binaryTermShiftQpowTrace_cost_le depth
          (arguments index)).trans
            (Nat.mul_le_mul_right
              (binaryTermCode (arguments index)).length hdepth)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermShiftQpowTrace depth
                  (arguments index)).2) ≤
            (100 * (budget + 1)) * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 ≤ binaryFormulaAtomHeaderCost 0 relationSymbol := by
        have htag := two_le_binaryNatCode_length 0
        dsimp [binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaAtomHeaderCost 0 relationSymbol) budget hheader
      simp only [binaryFormulaShiftQpowTrace, binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [binaryFormulaAtomHeaderCost] at hheader hcharge ⊢
      omega
  | depth, Semiformula.nrel relationSymbol arguments, budget, hbudget => by
      have hdepth : 16 + 50 * depth ≤ 100 * (budget + 1) := by
        have : depth ≤ budget := by
          have hone := one_le_formulaSymbolCount
            (Semiformula.nrel relationSymbol arguments)
          omega
        omega
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermShiftQpowTrace depth
                  (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (binaryTermShiftQpowTrace_cost_le depth
          (arguments index)).trans
            (Nat.mul_le_mul_right
              (binaryTermCode (arguments index)).length hdepth)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermShiftQpowTrace depth
                  (arguments index)).2) ≤
            (100 * (budget + 1)) * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 ≤ binaryFormulaAtomHeaderCost 1 relationSymbol := by
        have htag := two_le_binaryNatCode_length 1
        dsimp [binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaAtomHeaderCost 1 relationSymbol) budget hheader
      simp only [binaryFormulaShiftQpowTrace, binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [binaryFormulaAtomHeaderCost] at hheader hcharge ⊢
      omega
  | depth, left ⋏ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaShiftQpowTrace_cost_le
        depth left budget hleftBudget
      have hright := binaryFormulaShiftQpowTrace_cost_le
        depth right budget hrightBudget
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 4 := by
        have htag := two_le_binaryNatCode_length 4
        dsimp [binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 4) budget hheader
      simp only [binaryFormulaShiftQpowTrace, binaryFormulaCode,
        List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega
  | depth, left ⋎ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaShiftQpowTrace_cost_le
        depth left budget hleftBudget
      have hright := binaryFormulaShiftQpowTrace_cost_le
        depth right budget hrightBudget
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 5 := by
        simp [binaryFormulaNodeHeaderCost, binaryNatCode]
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 5) budget hheader
      simp only [binaryFormulaShiftQpowTrace, binaryFormulaCode,
        List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega
  | depth, ∀⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaShiftQpowTrace_cost_le
        (depth + 1) body budget hbodyBudget
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 6 := by
        simp [binaryFormulaNodeHeaderCost, binaryNatCode]
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 6) budget hheader
      simp only [binaryFormulaShiftQpowTrace, binaryFormulaCode,
        List.length_append]
      rw [Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega
  | depth, ∃⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaShiftQpowTrace_cost_le
        (depth + 1) body budget hbodyBudget
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 7 := by
        simp [binaryFormulaNodeHeaderCost, binaryNatCode]
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 7) budget hheader
      simp only [binaryFormulaShiftQpowTrace, binaryFormulaCode,
        List.length_append]
      rw [Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega

theorem binaryFormulaFreeQpowTrace_cost_le :
    ∀ (depth : Nat)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat (depth + 1))
      (budget : Nat),
      depth + formulaSymbolCount formula ≤ budget →
      (binaryFormulaFreeQpowTrace depth formula).2 ≤
        (100 * (budget + 1)) *
          (binaryFormulaCode formula).length
  | _, ⊤, budget, hbudget => by
      change
        2 * binaryFormulaNodeHeaderCost 2 + 3 ≤
          100 * (budget + 1) * binaryFormulaNodeHeaderCost 2
      apply binaryFormulaHeaderCharge_le
      have htag := two_le_binaryNatCode_length 2
      dsimp [binaryFormulaNodeHeaderCost]
      omega
  | _, ⊥, budget, hbudget => by
      change
        2 * binaryFormulaNodeHeaderCost 3 + 3 ≤
          100 * (budget + 1) * binaryFormulaNodeHeaderCost 3
      apply binaryFormulaHeaderCharge_le
      have htag := two_le_binaryNatCode_length 3
      dsimp [binaryFormulaNodeHeaderCost]
      omega
  | depth, Semiformula.rel relationSymbol arguments, budget, hbudget => by
      have hdepth : 16 + 50 * depth ≤ 100 * (budget + 1) := by
        have : depth ≤ budget := by
          have hone := one_le_formulaSymbolCount
            (Semiformula.rel relationSymbol arguments)
          omega
        omega
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFreeQpowTrace depth
                  (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (binaryTermFreeQpowTrace_cost_le depth
          (arguments index)).trans
            (Nat.mul_le_mul_right
              (binaryTermCode (arguments index)).length hdepth)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermFreeQpowTrace depth
                  (arguments index)).2) ≤
            (100 * (budget + 1)) * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 ≤ binaryFormulaAtomHeaderCost 0 relationSymbol := by
        have htag := two_le_binaryNatCode_length 0
        dsimp [binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaAtomHeaderCost 0 relationSymbol) budget hheader
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [binaryFormulaAtomHeaderCost] at hheader hcharge ⊢
      omega
  | depth, Semiformula.nrel relationSymbol arguments, budget, hbudget => by
      have hdepth : 16 + 50 * depth ≤ 100 * (budget + 1) := by
        have : depth ≤ budget := by
          have hone := one_le_formulaSymbolCount
            (Semiformula.nrel relationSymbol arguments)
          omega
        omega
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFreeQpowTrace depth
                  (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (binaryTermFreeQpowTrace_cost_le depth
          (arguments index)).trans
            (Nat.mul_le_mul_right
              (binaryTermCode (arguments index)).length hdepth)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermFreeQpowTrace depth
                  (arguments index)).2) ≤
            (100 * (budget + 1)) * Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                (100 * (budget + 1)) *
                  (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hheader :
          1 ≤ binaryFormulaAtomHeaderCost 1 relationSymbol := by
        have htag := two_le_binaryNatCode_length 1
        dsimp [binaryFormulaAtomHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaAtomHeaderCost 1 relationSymbol) budget hheader
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [binaryFormulaAtomHeaderCost] at hheader hcharge ⊢
      omega
  | depth, left ⋏ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaFreeQpowTrace_cost_le
        depth left budget hleftBudget
      have hright := binaryFormulaFreeQpowTrace_cost_le
        depth right budget hrightBudget
      have hleft' :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) left).2 ≤
            100 * (budget + 1) *
              (binaryFormulaCode left).length := by
        simpa only [binaryFormulaFreeQpowTrace] using hleft
      have hright' :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) right).2 ≤
            100 * (budget + 1) *
              (binaryFormulaCode right).length := by
        simpa only [binaryFormulaFreeQpowTrace] using hright
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 4 := by
        simp [binaryFormulaNodeHeaderCost, binaryNatCode]
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 4) budget hheader
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega
  | depth, left ⋎ right, budget, hbudget => by
      have hleftBudget :
          depth + formulaSymbolCount left ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := binaryFormulaFreeQpowTrace_cost_le
        depth left budget hleftBudget
      have hright := binaryFormulaFreeQpowTrace_cost_le
        depth right budget hrightBudget
      have hleft' :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) left).2 ≤
            100 * (budget + 1) *
              (binaryFormulaCode left).length := by
        simpa only [binaryFormulaFreeQpowTrace] using hleft
      have hright' :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace depth) right).2 ≤
            100 * (budget + 1) *
              (binaryFormulaCode right).length := by
        simpa only [binaryFormulaFreeQpowTrace] using hright
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 5 := by
        have htag := two_le_binaryNatCode_length 5
        dsimp [binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 5) budget hheader
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega
  | depth, ∀⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaFreeQpowTrace_cost_le
        (depth + 1) body budget hbodyBudget
      have hq :
          binaryTermQTrace (binaryTermFreeQpowTrace depth) =
            binaryTermFreeQpowTrace (depth + 1) := by
        funext term
        rfl
      have hbody' :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace (depth + 1)) body).2 ≤
            100 * (budget + 1) *
              (binaryFormulaCode body).length := by
        simpa only [binaryFormulaFreeQpowTrace] using hbody
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 6 := by
        have htag := two_le_binaryNatCode_length 6
        dsimp [binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 6) budget hheader
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [hq]
      rw [Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega
  | depth, ∃⁰ body, budget, hbudget => by
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body ≤ budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := binaryFormulaFreeQpowTrace_cost_le
        (depth + 1) body budget hbodyBudget
      have hq :
          binaryTermQTrace (binaryTermFreeQpowTrace depth) =
            binaryTermFreeQpowTrace (depth + 1) := by
        funext term
        rfl
      have hbody' :
          (binaryFormulaRewTrace
            (binaryTermFreeQpowTrace (depth + 1)) body).2 ≤
            100 * (budget + 1) *
              (binaryFormulaCode body).length := by
        simpa only [binaryFormulaFreeQpowTrace] using hbody
      have hheader : 1 ≤ binaryFormulaNodeHeaderCost 7 := by
        have htag := two_le_binaryNatCode_length 7
        dsimp [binaryFormulaNodeHeaderCost]
        omega
      have hcharge := binaryFormulaHeaderCharge_le
        (binaryFormulaNodeHeaderCost 7) budget hheader
      simp only [binaryFormulaFreeQpowTrace, binaryFormulaRewTrace,
        binaryFormulaCode, List.length_append]
      rw [hq]
      rw [Nat.mul_add]
      dsimp [binaryFormulaNodeHeaderCost] at hheader hcharge ⊢
      omega

theorem binaryFormulaShiftTrace_cost_le
    (formula : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaShiftTrace formula).2 ≤
      (100 * ((binaryFormulaCode formula).length + 1)) *
        (binaryFormulaCode formula).length := by
  let symbols := formulaSymbolCount formula
  let codeLength := (binaryFormulaCode formula).length
  have htrace := binaryFormulaShiftQpowTrace_cost_le 0 formula symbols
    (by simp [symbols])
  have hsymbols : symbols ≤ codeLength := by
    exact formulaSymbolCount_le_binaryFormulaCode_length formula
  calc
    (binaryFormulaShiftTrace formula).2 ≤
        (100 * (symbols + 1)) * codeLength := by
      simpa [binaryFormulaShiftTrace, symbols, codeLength] using htrace
    _ ≤ (100 * (codeLength + 1)) * codeLength :=
      Nat.mul_le_mul_right codeLength
        (Nat.mul_le_mul_left 100 (by omega))

theorem binaryFormulaFreeTrace_cost_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaFreeTrace formula).2 ≤
      (100 * ((binaryFormulaCode formula).length + 1)) *
        (binaryFormulaCode formula).length := by
  let symbols := formulaSymbolCount formula
  let codeLength := (binaryFormulaCode formula).length
  have htrace := binaryFormulaFreeQpowTrace_cost_le 0 formula symbols
    (by simp [symbols])
  have hsymbols : symbols ≤ codeLength := by
    exact formulaSymbolCount_le_binaryFormulaCode_length formula
  calc
    (binaryFormulaFreeTrace formula).2 ≤
        (100 * (symbols + 1)) * codeLength := by
      simpa [binaryFormulaFreeTrace, symbols, codeLength] using htrace
    _ ≤ (100 * (codeLength + 1)) * codeLength :=
      Nat.mul_le_mul_right codeLength
        (Nat.mul_le_mul_left 100 (by omega))

/-! ## Formula-list shift trace -/

def formulaListShiftTrace :
    List LO.FirstOrder.ArithmeticProposition →
      SyntaxTrace (List LO.FirstOrder.ArithmeticProposition)
  | [] => ([], 1)
  | formula :: formulas =>
      let head := binaryFormulaShiftTrace formula
      let tail := formulaListShiftTrace formulas
      (head.1 :: tail.1, head.2 + tail.2 + 1)

theorem formulaListShiftTrace_result
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    (formulaListShiftTrace formulas).1 =
      formulas.map Rewriting.shift := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp [formulaListShiftTrace,
        binaryFormulaShiftTrace_result, ih]

theorem formulaListShiftTrace_cost_le_budget
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    ∀ budget,
      formulaListCodeWeight formulas ≤ budget →
      (formulaListShiftTrace formulas).2 ≤
        (100 * (budget + 1) + 1) *
          formulaListCodeWeight formulas + 1 := by
  induction formulas with
  | nil =>
      intro budget hbudget
      simp [formulaListShiftTrace]
  | cons formula formulas ih =>
      intro budget hbudget
      let headLength := (binaryFormulaCode formula).length
      let tailWeight := formulaListCodeWeight formulas
      have hheadLength : headLength ≤ budget := by
        simp only [formulaListCodeWeight_cons] at hbudget
        dsimp [headLength]
        omega
      have htailWeight : tailWeight ≤ budget := by
        simp only [formulaListCodeWeight_cons] at hbudget
        dsimp [tailWeight]
        omega
      have hhead := binaryFormulaShiftTrace_cost_le formula
      have hheadFactor :
          100 * (headLength + 1) ≤ 100 * (budget + 1) + 1 := by
        omega
      have hheadScaled :
          (binaryFormulaShiftTrace formula).2 ≤
            (100 * (budget + 1) + 1) * headLength := by
        calc
          _ ≤ (100 * (headLength + 1)) * headLength := by
            simpa [headLength] using hhead
          _ ≤ (100 * (budget + 1) + 1) * headLength :=
            Nat.mul_le_mul_right headLength hheadFactor
      have htail := ih budget htailWeight
      simp only [formulaListShiftTrace, formulaListCodeWeight_cons]
      rw [Nat.mul_add, Nat.mul_add]
      dsimp [headLength, tailWeight] at hheadScaled htail ⊢
      omega

theorem formulaListShiftTrace_cost_le
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    (formulaListShiftTrace formulas).2 ≤
      (100 * (formulaListCodeWeight formulas + 1) + 1) *
        formulaListCodeWeight formulas + 1 := by
  exact formulaListShiftTrace_cost_le_budget formulas
    (formulaListCodeWeight formulas) le_rfl

/-! ## Bit-level natural comparison and maximum

`Nat.bits` is little-endian.  The recursive comparison therefore inspects
the tails first: a tail contains all more-significant bits.  On canonical
`Nat.bits` lists, exhausting one tail before the other also decides the
ordering.  The public wrappers explicitly charge materializing both bit
lists in addition to the recursive comparison.
-/

def binaryBitsCompareTrace :
    List Bool → List Bool → SyntaxTrace Ordering
  | [], [] => (.eq, 1)
  | [], _ :: _ => (.lt, 1)
  | _ :: _, [] => (.gt, 1)
  | leftBit :: leftBits, rightBit :: rightBits =>
      let higher := binaryBitsCompareTrace leftBits rightBits
      match higher.1 with
      | .lt => (.lt, higher.2 + 1)
      | .gt => (.gt, higher.2 + 1)
      | .eq =>
          match leftBit, rightBit with
          | false, true => (.lt, higher.2 + 1)
          | true, false => (.gt, higher.2 + 1)
          | _, _ => (.eq, higher.2 + 1)

theorem binaryBitsCompareTrace_cost_le
    (leftBits rightBits : List Bool) :
    (binaryBitsCompareTrace leftBits rightBits).2 ≤
      leftBits.length + rightBits.length + 1 := by
  induction leftBits generalizing rightBits with
  | nil =>
      cases rightBits <;> simp [binaryBitsCompareTrace]
  | cons leftBit leftBits ih =>
      cases rightBits with
      | nil => simp [binaryBitsCompareTrace]
      | cons rightBit rightBits =>
          have htail := ih rightBits
          simp only [binaryBitsCompareTrace]
          generalize hcomparison :
            binaryBitsCompareTrace leftBits rightBits = comparison
          rcases comparison with ⟨ordering, cost⟩
          cases ordering <;> cases leftBit <;> cases rightBit <;>
            simp_all <;> omega

theorem binaryBitsCompareTrace_natBits_result
    (left right : Nat) :
    (binaryBitsCompareTrace left.bits right.bits).1 =
      compare left right := by
  induction left using Nat.binaryRec' generalizing right with
  | zero =>
      induction right using Nat.binaryRec' with
      | zero => simp [binaryBitsCompareTrace]
      | bit rightBit rightHigh hrightHigh ihRight =>
          have hrightNe : Nat.bit rightBit rightHigh ≠ 0 := by
            simpa [Nat.bit_eq_zero_iff] using hrightHigh
          have hrightPos : 0 < Nat.bit rightBit rightHigh :=
            Nat.pos_of_ne_zero hrightNe
          have hcomparison :
              compare 0 (Nat.bit rightBit rightHigh) = .lt :=
            compare_lt_iff_lt.mpr hrightPos
          rw [Nat.zero_bits,
            Nat.bits_append_bit rightHigh rightBit hrightHigh]
          simpa [binaryBitsCompareTrace] using hcomparison.symm
  | bit leftBit leftHigh hleftHigh ihLeft =>
      induction right using Nat.binaryRec' with
      | zero =>
          have hleftNe : Nat.bit leftBit leftHigh ≠ 0 := by
            simpa [Nat.bit_eq_zero_iff] using hleftHigh
          have hleftPos : 0 < Nat.bit leftBit leftHigh :=
            Nat.pos_of_ne_zero hleftNe
          have hcomparison :
              compare (Nat.bit leftBit leftHigh) 0 = .gt :=
            compare_gt_iff_gt.mpr hleftPos
          rw [Nat.bits_append_bit leftHigh leftBit hleftHigh,
            Nat.zero_bits]
          simpa [binaryBitsCompareTrace] using hcomparison.symm
      | bit rightBit rightHigh hrightHigh ihRight =>
          rw [Nat.bits_append_bit leftHigh leftBit hleftHigh,
            Nat.bits_append_bit rightHigh rightBit hrightHigh]
          simp only [binaryBitsCompareTrace]
          rw [ihLeft rightHigh]
          rcases lt_trichotomy leftHigh rightHigh with
            hhigh | hhigh | hhigh
          · have hhigher : compare leftHigh rightHigh = .lt :=
              compare_lt_iff_lt.mpr hhigh
            have htotal :
                compare (Nat.bit leftBit leftHigh)
                    (Nat.bit rightBit rightHigh) = .lt :=
              compare_lt_iff_lt.mpr
                (Nat.bit_lt_bit leftBit rightBit hhigh)
            simp [hhigher, htotal]
          · subst rightHigh
            cases leftBit <;> cases rightBit
            · simp [binaryBitsCompareTrace]
            · have htotal :
                  compare (Nat.bit false leftHigh)
                      (Nat.bit true leftHigh) = .lt :=
                compare_lt_iff_lt.mpr (by simp [Nat.bit])
              have hhigh : compare leftHigh leftHigh = .eq :=
                compare_eq_iff_eq.mpr rfl
              simp only [hhigh]
              exact htotal.symm
            · have htotal :
                  compare (Nat.bit true leftHigh)
                      (Nat.bit false leftHigh) = .gt :=
                compare_gt_iff_gt.mpr (by simp [Nat.bit])
              have hhigh : compare leftHigh leftHigh = .eq :=
                compare_eq_iff_eq.mpr rfl
              simp only [hhigh]
              exact htotal.symm
            · simp [binaryBitsCompareTrace]
          · have hhigher : compare leftHigh rightHigh = .gt :=
              compare_gt_iff_gt.mpr hhigh
            have htotal :
                compare (Nat.bit leftBit leftHigh)
                    (Nat.bit rightBit rightHigh) = .gt :=
              compare_gt_iff_gt.mpr
                (Nat.bit_lt_bit rightBit leftBit hhigh)
            simp [hhigher, htotal]

def binaryNatCompareTrace (left right : Nat) :
    SyntaxTrace Ordering :=
  let comparison := binaryBitsCompareTrace left.bits right.bits
  (comparison.1,
    comparison.2 + left.bits.length + right.bits.length + 1)

theorem binaryNatCompareTrace_result (left right : Nat) :
    (binaryNatCompareTrace left right).1 = compare left right := by
  simp [binaryNatCompareTrace,
    binaryBitsCompareTrace_natBits_result]

theorem binaryNatCompareTrace_cost_le (left right : Nat) :
    (binaryNatCompareTrace left right).2 ≤
      2 * (Nat.size left + Nat.size right) + 2 := by
  have hcomparison :=
    binaryBitsCompareTrace_cost_le left.bits right.bits
  simp only [binaryNatCompareTrace]
  calc
    (binaryBitsCompareTrace left.bits right.bits).2 +
          left.bits.length + right.bits.length + 1 ≤
        2 * (left.bits.length + right.bits.length) + 2 := by
      omega
    _ = 2 * (Nat.size left + Nat.size right) + 2 := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]

def binaryNatLeTrace (left right : Nat) : SyntaxTrace Bool :=
  let comparison := binaryNatCompareTrace left right
  match comparison.1 with
  | .gt => (false, comparison.2 + 1)
  | .eq => (true, comparison.2 + 1)
  | .lt => (true, comparison.2 + 1)

theorem binaryNatLeTrace_result_eq_true_iff (left right : Nat) :
    (binaryNatLeTrace left right).1 = true ↔ left ≤ right := by
  rw [binaryNatLeTrace, binaryNatCompareTrace_result]
  cases hcomparison : compare left right with
  | lt =>
      have hlt : left < right := compare_lt_iff_lt.mp hcomparison
      simp [hcomparison, hlt.le]
  | eq =>
      have heq : left = right := compare_eq_iff_eq.mp hcomparison
      simp [hcomparison, heq]
  | gt =>
      have hgt : right < left := compare_gt_iff_gt.mp hcomparison
      simp [hcomparison, Nat.not_le_of_lt hgt]

theorem binaryNatLeTrace_cost_le (left right : Nat) :
    (binaryNatLeTrace left right).2 ≤
      2 * (Nat.size left + Nat.size right) + 3 := by
  have hcomparison := binaryNatCompareTrace_cost_le left right
  cases horder : (binaryNatCompareTrace left right).1 <;>
    simp [binaryNatLeTrace, horder] <;> omega

def binaryNatMaxTrace (left right : Nat) : SyntaxTrace Nat :=
  let comparison := binaryNatCompareTrace left right
  match comparison.1 with
  | .gt => (left, comparison.2 + 1)
  | .eq => (right, comparison.2 + 1)
  | .lt => (right, comparison.2 + 1)

theorem binaryNatMaxTrace_result (left right : Nat) :
    (binaryNatMaxTrace left right).1 = max left right := by
  simp only [binaryNatMaxTrace, binaryNatCompareTrace_result]
  cases hcomparison : compare left right with
  | lt =>
      have hle : left ≤ right :=
        (compare_lt_iff_lt.mp hcomparison).le
      simp [hcomparison, max_eq_right hle]
  | eq =>
      have heq : left = right :=
        compare_eq_iff_eq.mp hcomparison
      simp [hcomparison, heq]
  | gt =>
      have hle : right ≤ left :=
        (compare_gt_iff_gt.mp hcomparison).le
      simp [hcomparison, max_eq_left hle]

theorem binaryNatMaxTrace_cost_le (left right : Nat) :
    (binaryNatMaxTrace left right).2 ≤
      2 * (Nat.size left + Nat.size right) + 3 := by
  have hcomparison := binaryNatCompareTrace_cost_le left right
  cases horder : (binaryNatCompareTrace left right).1 <;>
    simp [binaryNatMaxTrace, horder] <;> omega

/-! ## Structural free-variable supremum

`listFvSup` is the executable specification: it is zero on an empty list and
otherwise one more than the largest listed free-variable index.  Formula and
term traces below compute that value while charging each binary maximum.
-/

def listFvSup : List Nat → Nat
  | [] => 0
  | index :: indices => max (index + 1) (listFvSup indices)

def listNatMax : List Nat → Nat
  | [] => 0
  | value :: values => max value (listNatMax values)

@[simp] theorem listFvSup_append (left right : List Nat) :
    listFvSup (left ++ right) =
      max (listFvSup left) (listFvSup right) := by
  induction left with
  | nil => simp [listFvSup]
  | cons index indices ih =>
      simp [listFvSup, ih, max_assoc]

theorem listFvSup_flatten_matrix {arity : Nat}
    (lists : Fin arity → List Nat) :
    listFvSup (List.flatten (Matrix.toList lists)) =
      listNatMax (Matrix.toList (fun index => listFvSup (lists index))) := by
  induction arity with
  | zero => simp [listFvSup, listNatMax]
  | succ arity ih =>
      rw [Matrix.toList_succ, List.flatten_cons, listFvSup_append,
        Matrix.toList_succ]
      simp only [listNatMax]
      have htail := ih (lists := lists ∘ Fin.succ)
      have hcongr := congrArg
        (fun value => max (listFvSup (lists 0)) value) htail
      simpa [Function.comp_def] using hcongr

theorem mem_lt_listFvSup {index : Nat} {indices : List Nat}
    (hmem : index ∈ indices) :
    index < listFvSup indices := by
  induction indices with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [listFvSup]
      rcases hmem with rfl | hmem
      · exact lt_of_lt_of_le (Nat.lt_succ_self index)
          (le_max_left _ _)
      · exact (ih hmem).trans_le (le_max_right _ _)

theorem pred_mem_of_listFvSup_pos (indices : List Nat)
    (hpos : 0 < listFvSup indices) :
    listFvSup indices - 1 ∈ indices := by
  induction indices with
  | nil => simp [listFvSup] at hpos
  | cons head tail ih =>
      simp only [listFvSup] at hpos ⊢
      by_cases hleft : tail = []
      · subst tail
        simp [listFvSup]
      · by_cases hmax : head + 1 ≤ listFvSup tail
        · have htailPos : 0 < listFvSup tail := by omega
          have hvalue :
              max (head + 1) (listFvSup tail) = listFvSup tail :=
            max_eq_right hmax
          rw [hvalue]
          exact List.mem_cons_of_mem head (ih htailPos)
        · have hvalue :
              max (head + 1) (listFvSup tail) = head + 1 :=
            max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hmax))
          rw [hvalue]
          simp

theorem listNatMax_size_le (values : List Nat) (budget : Nat)
    (hvalues : ∀ value ∈ values, Nat.size value ≤ budget) :
    Nat.size (listNatMax values) ≤ budget := by
  induction values with
  | nil => simp [listNatMax]
  | cons value values ih =>
      have hvalue := hvalues value (by simp)
      have htail : ∀ item ∈ values, Nat.size item ≤ budget := by
        intro item hitem
        exact hvalues item (by simp [hitem])
      have hrest := ih htail
      simp only [listNatMax]
      rcases le_total value (listNatMax values) with hle | hle
      · rw [max_eq_right hle]
        exact hrest
      · rw [max_eq_left hle]
        exact hvalue

def binaryNatMaxListTrace : List Nat → SyntaxTrace Nat
  | [] => (0, 1)
  | value :: values =>
      let tail := binaryNatMaxListTrace values
      let maximum := binaryNatMaxTrace value tail.1
      (maximum.1, tail.2 + maximum.2 + 1)

theorem binaryNatMaxListTrace_result (values : List Nat) :
    (binaryNatMaxListTrace values).1 = listNatMax values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [binaryNatMaxListTrace, binaryNatMaxTrace_result, ih,
        listNatMax]

theorem binaryNatMaxListTrace_cost_le
    (values : List Nat) (budget : Nat)
    (hvalues : ∀ value ∈ values, Nat.size value ≤ budget) :
    (binaryNatMaxListTrace values).2 ≤
      (4 * budget + 4) * (values.length + 1) := by
  induction values with
  | nil => simp [binaryNatMaxListTrace]
  | cons value values ih =>
      have hvalue := hvalues value (by simp)
      have htail : ∀ item ∈ values, Nat.size item ≤ budget := by
        intro item hitem
        exact hvalues item (by simp [hitem])
      have htailCost := ih htail
      have htailSize := listNatMax_size_le values budget htail
      have hmaximum := binaryNatMaxTrace_cost_le value
        (binaryNatMaxListTrace values).1
      rw [binaryNatMaxListTrace_result] at hmaximum
      have hmaximum' :
          (binaryNatMaxTrace value
              (binaryNatMaxListTrace values).1).2 ≤
            4 * budget + 3 := by
        calc
          (binaryNatMaxTrace value
              (binaryNatMaxListTrace values).1).2 ≤
              2 * (Nat.size value +
                Nat.size (listNatMax values)) + 3 := by
            simpa only [binaryNatMaxListTrace_result] using hmaximum
          _ ≤ 4 * budget + 3 := by omega
      simp only [binaryNatMaxListTrace, List.length_cons]
      rw [Nat.mul_add]
      omega

def binaryTermFvSupTrace {arity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat arity → SyntaxTrace Nat
  | term@(#_) => (0, (binaryTermCode term).length + 1)
  | term@(&index) =>
      (index + 1,
        (binaryTermCode term).length +
          (binaryNatCode (index + 1)).length + 3)
  | Semiterm.func functionSymbol arguments =>
      let traces := fun index => binaryTermFvSupTrace (arguments index)
      let values := Matrix.toList (fun index => (traces index).1)
      let maximum := binaryNatMaxListTrace values
      (maximum.1,
        2 * binaryTermFunctionHeaderCost functionSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2) +
          maximum.2)

def binaryFormulaFvSupTrace :
    {arity : Nat} →
      LO.FirstOrder.ArithmeticSemiformula Nat arity → SyntaxTrace Nat
  | _, ⊤ => (0, 2 * binaryFormulaNodeHeaderCost 2 + 3)
  | _, ⊥ => (0, 2 * binaryFormulaNodeHeaderCost 3 + 3)
  | _, Semiformula.rel relationSymbol arguments =>
      let traces := fun index => binaryTermFvSupTrace (arguments index)
      let values := Matrix.toList (fun index => (traces index).1)
      let maximum := binaryNatMaxListTrace values
      (maximum.1,
        2 * binaryFormulaAtomHeaderCost 0 relationSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2) +
          maximum.2)
  | _, Semiformula.nrel relationSymbol arguments =>
      let traces := fun index => binaryTermFvSupTrace (arguments index)
      let values := Matrix.toList (fun index => (traces index).1)
      let maximum := binaryNatMaxListTrace values
      (maximum.1,
        2 * binaryFormulaAtomHeaderCost 1 relationSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2) +
          maximum.2)
  | _, left ⋏ right =>
      let leftTrace := binaryFormulaFvSupTrace left
      let rightTrace := binaryFormulaFvSupTrace right
      let maximum := binaryNatMaxTrace leftTrace.1 rightTrace.1
      (maximum.1,
        leftTrace.2 + rightTrace.2 + maximum.2 +
          2 * binaryFormulaNodeHeaderCost 4 + 3)
  | _, left ⋎ right =>
      let leftTrace := binaryFormulaFvSupTrace left
      let rightTrace := binaryFormulaFvSupTrace right
      let maximum := binaryNatMaxTrace leftTrace.1 rightTrace.1
      (maximum.1,
        leftTrace.2 + rightTrace.2 + maximum.2 +
          2 * binaryFormulaNodeHeaderCost 5 + 3)
  | _, ∀⁰ body =>
      let bodyTrace := binaryFormulaFvSupTrace body
      (bodyTrace.1,
        bodyTrace.2 + 2 * binaryFormulaNodeHeaderCost 6 + 3)
  | _, ∃⁰ body =>
      let bodyTrace := binaryFormulaFvSupTrace body
      (bodyTrace.1,
        bodyTrace.2 + 2 * binaryFormulaNodeHeaderCost 7 + 3)

theorem binaryTermFvSupTrace_result {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermFvSupTrace term).1 = listFvSup term.fvarList := by
  induction term with
  | bvar index => rfl
  | fvar index => rfl
  | func functionSymbol arguments ih =>
      simp only [binaryTermFvSupTrace,
        binaryNatMaxListTrace_result, Semiterm.fvarList]
      rw [listFvSup_flatten_matrix]
      congr 1
      apply congrArg Matrix.toList
      funext index
      exact ih index

theorem binaryFormulaFvSupTrace_list_result :
    ∀ {arity : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity),
      (binaryFormulaFvSupTrace formula).1 =
        listFvSup formula.fvarList
  | _, ⊤ => rfl
  | _, ⊥ => rfl
  | _, Semiformula.rel relationSymbol arguments => by
      simp only [binaryFormulaFvSupTrace,
        binaryNatMaxListTrace_result, Semiformula.fvarList]
      rw [listFvSup_flatten_matrix]
      congr 1
      apply congrArg Matrix.toList
      funext index
      exact binaryTermFvSupTrace_result (arguments index)
  | _, Semiformula.nrel relationSymbol arguments => by
      simp only [binaryFormulaFvSupTrace,
        binaryNatMaxListTrace_result, Semiformula.fvarList]
      rw [listFvSup_flatten_matrix]
      congr 1
      apply congrArg Matrix.toList
      funext index
      exact binaryTermFvSupTrace_result (arguments index)
  | _, left ⋏ right => by
      simp [binaryFormulaFvSupTrace,
        binaryNatMaxTrace_result, listFvSup_append,
        binaryFormulaFvSupTrace_list_result left,
        binaryFormulaFvSupTrace_list_result right,
        Semiformula.fvarList]
  | _, left ⋎ right => by
      simp [binaryFormulaFvSupTrace,
        binaryNatMaxTrace_result, listFvSup_append,
        binaryFormulaFvSupTrace_list_result left,
        binaryFormulaFvSupTrace_list_result right,
        Semiformula.fvarList]
  | _, ∀⁰ body => by
      simpa [binaryFormulaFvSupTrace, Semiformula.fvarList] using
        binaryFormulaFvSupTrace_list_result body
  | _, ∃⁰ body => by
      simpa [binaryFormulaFvSupTrace, Semiformula.fvarList] using
        binaryFormulaFvSupTrace_list_result body

theorem fvar_pred_of_fvSup_pos {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (hpos : 0 < formula.fvSup) :
    formula.FVar? (formula.fvSup - 1) := by
  by_cases hempty : formula.freeVariables = ∅
  · simp [Semiformula.fvSup, hempty] at hpos
  · obtain ⟨maximum, hmaximum⟩ :=
      Finset.max_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hempty)
    rw [show formula.fvSup = maximum + 1 from by
      simp [Semiformula.fvSup, hmaximum]]
    simpa using Finset.mem_of_max hmaximum

theorem listFvSup_formula_eq_fvSup {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    listFvSup formula.fvarList = formula.fvSup := by
  apply Nat.le_antisymm
  · by_cases hzero : listFvSup formula.fvarList = 0
    · simpa [hzero] using Nat.zero_le formula.fvSup
    · have hpos : 0 < listFvSup formula.fvarList :=
          Nat.pos_of_ne_zero hzero
      have hmem := pred_mem_of_listFvSup_pos formula.fvarList hpos
      have hfvar :
          formula.FVar? (listFvSup formula.fvarList - 1) :=
        Semiformula.mem_fvarList_iff_fvar?.mp hmem
      have hlt := Semiformula.lt_fvSup_of_fvar? hfvar
      omega
  · by_cases hzero : formula.fvSup = 0
    · simpa [hzero] using Nat.zero_le (listFvSup formula.fvarList)
    · have hpos : 0 < formula.fvSup := Nat.pos_of_ne_zero hzero
      have hfvar := fvar_pred_of_fvSup_pos formula hpos
      have hmem : formula.fvSup - 1 ∈ formula.fvarList :=
        Semiformula.mem_fvarList_iff_fvar?.mpr hfvar
      have hlt := mem_lt_listFvSup hmem
      omega

theorem binaryFormulaFvSupTrace_result {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaFvSupTrace formula).1 = formula.fvSup := by
  rw [binaryFormulaFvSupTrace_list_result,
    listFvSup_formula_eq_fvSup]

theorem binaryTermFvSupTrace_size_le_code {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    Nat.size (binaryTermFvSupTrace term).1 ≤
      (binaryTermCode term).length := by
  induction term with
  | bvar index => simp [binaryTermFvSupTrace]
  | fvar index =>
      have hsize := natSize_add_one_le index
      simp only [binaryTermFvSupTrace]
      simp [binaryTermCode,
        FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
      omega
  | func functionSymbol arguments ih =>
      let values := Matrix.toList
        (fun index => (binaryTermFvSupTrace (arguments index)).1)
      have hchild (index : Fin _) :
          (binaryTermCode (arguments index)).length ≤
            (binaryTermCode
              (Semiterm.func functionSymbol arguments)).length := by
        have hsingle :
            (binaryTermCode (arguments index)).length ≤
              Finset.univ.sum
                (fun child =>
                  (binaryTermCode (arguments child)).length) :=
          Finset.single_le_sum
            (fun child _ => Nat.zero_le
              (binaryTermCode (arguments child)).length)
            (Finset.mem_univ index)
        simp only [binaryTermCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hvalues : ∀ value ∈ values,
          Nat.size value ≤
            (binaryTermCode
              (Semiterm.func functionSymbol arguments)).length := by
        intro value hvalue
        rw [Matrix.mem_toList_iff] at hvalue
        rcases hvalue with ⟨index, hindex⟩
        rw [← hindex]
        exact (ih index).trans (hchild index)
      have hmaximum := listNatMax_size_le values
        (binaryTermCode
          (Semiterm.func functionSymbol arguments)).length hvalues
      simpa only [binaryTermFvSupTrace,
        binaryNatMaxListTrace_result, values] using hmaximum

theorem binaryFormulaFvSupTrace_size_le_code :
    ∀ {arity : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity),
      Nat.size (binaryFormulaFvSupTrace formula).1 ≤
        (binaryFormulaCode formula).length
  | _, ⊤ => by simp [binaryFormulaFvSupTrace, binaryFormulaCode]
  | _, ⊥ => by simp [binaryFormulaFvSupTrace, binaryFormulaCode]
  | _, Semiformula.rel relationSymbol arguments => by
      let values := Matrix.toList
        (fun index => (binaryTermFvSupTrace (arguments index)).1)
      have hchild (index : Fin _) :
          (binaryTermCode (arguments index)).length ≤
            (binaryFormulaCode
              (Semiformula.rel relationSymbol arguments)).length := by
        have hsingle :
            (binaryTermCode (arguments index)).length ≤
              Finset.univ.sum
                (fun child =>
                  (binaryTermCode (arguments child)).length) :=
          Finset.single_le_sum
            (fun child _ => Nat.zero_le
              (binaryTermCode (arguments child)).length)
            (Finset.mem_univ index)
        simp only [binaryFormulaCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hvalues : ∀ value ∈ values,
          Nat.size value ≤
            (binaryFormulaCode
              (Semiformula.rel relationSymbol arguments)).length := by
        intro value hvalue
        rw [Matrix.mem_toList_iff] at hvalue
        rcases hvalue with ⟨index, hindex⟩
        rw [← hindex]
        exact (binaryTermFvSupTrace_size_le_code
          (arguments index)).trans (hchild index)
      have hmaximum := listNatMax_size_le values
        (binaryFormulaCode
          (Semiformula.rel relationSymbol arguments)).length hvalues
      simpa only [binaryFormulaFvSupTrace,
        binaryNatMaxListTrace_result, values] using hmaximum
  | _, Semiformula.nrel relationSymbol arguments => by
      let values := Matrix.toList
        (fun index => (binaryTermFvSupTrace (arguments index)).1)
      have hchild (index : Fin _) :
          (binaryTermCode (arguments index)).length ≤
            (binaryFormulaCode
              (Semiformula.nrel relationSymbol arguments)).length := by
        have hsingle :
            (binaryTermCode (arguments index)).length ≤
              Finset.univ.sum
                (fun child =>
                  (binaryTermCode (arguments child)).length) :=
          Finset.single_le_sum
            (fun child _ => Nat.zero_le
              (binaryTermCode (arguments child)).length)
            (Finset.mem_univ index)
        simp only [binaryFormulaCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hvalues : ∀ value ∈ values,
          Nat.size value ≤
            (binaryFormulaCode
              (Semiformula.nrel relationSymbol arguments)).length := by
        intro value hvalue
        rw [Matrix.mem_toList_iff] at hvalue
        rcases hvalue with ⟨index, hindex⟩
        rw [← hindex]
        exact (binaryTermFvSupTrace_size_le_code
          (arguments index)).trans (hchild index)
      have hmaximum := listNatMax_size_le values
        (binaryFormulaCode
          (Semiformula.nrel relationSymbol arguments)).length hvalues
      simpa only [binaryFormulaFvSupTrace,
        binaryNatMaxListTrace_result, values] using hmaximum
  | _, left ⋏ right => by
      have hleft := binaryFormulaFvSupTrace_size_le_code left
      have hright := binaryFormulaFvSupTrace_size_le_code right
      have hleftCode :
          (binaryFormulaCode left).length ≤
            (binaryFormulaCode (left ⋏ right)).length := by
        have htag := two_le_binaryNatCode_length 4
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hrightCode :
          (binaryFormulaCode right).length ≤
            (binaryFormulaCode (left ⋏ right)).length := by
        have htag := two_le_binaryNatCode_length 4
        simp only [binaryFormulaCode, List.length_append]
        omega
      simp only [binaryFormulaFvSupTrace,
        binaryNatMaxTrace_result]
      rcases le_total
          (binaryFormulaFvSupTrace left).1
          (binaryFormulaFvSupTrace right).1 with hle | hle
      · rw [max_eq_right hle]
        exact hright.trans hrightCode
      · rw [max_eq_left hle]
        exact hleft.trans hleftCode
  | _, left ⋎ right => by
      have hleft := binaryFormulaFvSupTrace_size_le_code left
      have hright := binaryFormulaFvSupTrace_size_le_code right
      have hleftCode :
          (binaryFormulaCode left).length ≤
            (binaryFormulaCode (left ⋎ right)).length := by
        have htag := two_le_binaryNatCode_length 5
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hrightCode :
          (binaryFormulaCode right).length ≤
            (binaryFormulaCode (left ⋎ right)).length := by
        have htag := two_le_binaryNatCode_length 5
        simp only [binaryFormulaCode, List.length_append]
        omega
      simp only [binaryFormulaFvSupTrace,
        binaryNatMaxTrace_result]
      rcases le_total
          (binaryFormulaFvSupTrace left).1
          (binaryFormulaFvSupTrace right).1 with hle | hle
      · rw [max_eq_right hle]
        exact hright.trans hrightCode
      · rw [max_eq_left hle]
        exact hleft.trans hleftCode
  | _, ∀⁰ body => by
      have hbody := binaryFormulaFvSupTrace_size_le_code body
      simp only [binaryFormulaFvSupTrace, binaryFormulaCode,
        List.length_append]
      omega
  | _, ∃⁰ body => by
      have hbody := binaryFormulaFvSupTrace_size_le_code body
      simp only [binaryFormulaFvSupTrace, binaryFormulaCode,
        List.length_append]
      omega

theorem binaryTermFvSupTrace_cost_le_budget {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    ∀ budget,
      (binaryTermCode term).length ≤ budget →
      (binaryTermFvSupTrace term).2 ≤
        (100 * (budget + 1)) *
          (binaryTermCode term).length * termSymbolCount term := by
  induction term with
  | bvar index =>
      intro budget hbudget
      have hlength := four_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have hfactor : 3 ≤ 100 * (budget + 1) := by omega
      have hscaled := Nat.mul_le_mul_right
        (binaryTermCode
          (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length
        hfactor
      simpa [binaryTermFvSupTrace, termSymbolCount] using
        (show
          (binaryTermCode
              (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length +
              1 ≤
            (100 * (budget + 1)) *
              (binaryTermCode
                (#index : LO.FirstOrder.ArithmeticSemiterm Nat arity)).length
          by omega)
  | fvar index =>
      intro budget hbudget
      let input :=
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat arity)
      have hlength := four_le_binaryTermCode_length input
      have hsize := natSize_add_one_le index
      have houtput :
          (binaryNatCode (index + 1)).length ≤
            (binaryTermCode input).length := by
        dsimp [input]
        simp only [binaryTermCode, List.length_append,
          FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
        omega
      have hfactor : 3 ≤ 100 * (budget + 1) := by omega
      have hscaled := Nat.mul_le_mul_right
        (binaryTermCode input).length hfactor
      simpa [binaryTermFvSupTrace, termSymbolCount, input] using
        (show
          (binaryTermCode input).length +
              (binaryNatCode (index + 1)).length + 3 ≤
            (100 * (budget + 1)) *
              (binaryTermCode input).length
          by omega)
  | func functionSymbol arguments ih =>
      intro budget hbudget
      rename_i functionArity
      let codeLength :=
        (binaryTermCode
          (Semiterm.func functionSymbol arguments)).length
      let symbols := termSymbolCount
        (Semiterm.func functionSymbol arguments)
      let factor := 100 * (budget + 1)
      let header := binaryTermFunctionHeaderCost functionSymbol
      let values := Matrix.toList
        (fun index => (binaryTermFvSupTrace (arguments index)).1)
      have hchild (index : Fin functionArity) :
          (binaryTermCode (arguments index)).length ≤ codeLength := by
        have hsingle :
            (binaryTermCode (arguments index)).length ≤
              Finset.univ.sum
                (fun child =>
                  (binaryTermCode (arguments child)).length) :=
          Finset.single_le_sum
            (fun child _ => Nat.zero_le
              (binaryTermCode (arguments child)).length)
            (Finset.mem_univ index)
        dsimp [codeLength, header, binaryTermFunctionHeaderCost]
        simp only [binaryTermCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFvSupTrace (arguments index)).2) ≤
            Finset.univ.sum
              (fun index =>
                factor * codeLength *
                  termSymbolCount (arguments index)) := by
        apply Finset.sum_le_sum
        intro index hindex
        have hrecursive := ih index budget
          ((hchild index).trans hbudget)
        exact hrecursive.trans
          (Nat.mul_le_mul_right (termSymbolCount (arguments index))
            (Nat.mul_le_mul_left factor (hchild index)))
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermFvSupTrace (arguments index)).2) ≤
            factor * codeLength *
              Finset.univ.sum
                (fun index => termSymbolCount (arguments index)) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                factor * codeLength *
                  termSymbolCount (arguments index)) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hvalues : ∀ value ∈ values,
          Nat.size value ≤ budget := by
        intro value hvalue
        rw [Matrix.mem_toList_iff] at hvalue
        rcases hvalue with ⟨index, hindex⟩
        rw [← hindex]
        exact (binaryTermFvSupTrace_size_le_code
          (arguments index)).trans ((hchild index).trans hbudget)
      have hmaximumRaw :=
        binaryNatMaxListTrace_cost_le values budget hvalues
      have harity : functionArity + 1 ≤ symbols := by
        have hsum : functionArity ≤
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index)) := by
          calc
            functionArity = Finset.univ.sum (fun _ : Fin functionArity => 1) := by
              simp
            _ ≤ Finset.univ.sum
                (fun index => termSymbolCount (arguments index)) :=
              Finset.sum_le_sum (fun index _ =>
                one_le_termSymbolCount (arguments index))
        dsimp [symbols]
        simp only [termSymbolCount]
        omega
      have hsymbolsCode : symbols ≤ codeLength := by
        exact termSymbolCount_le_binaryTermCode_length
          (Semiterm.func functionSymbol arguments)
      have hmaximum :
          (binaryNatMaxListTrace values).2 ≤
            (4 * budget + 4) * codeLength := by
        have hlength : values.length = functionArity := by
          simp [values]
        rw [hlength] at hmaximumRaw
        exact hmaximumRaw.trans
          (Nat.mul_le_mul_left (4 * budget + 4)
            (harity.trans hsymbolsCode))
      have hheaderCode : header ≤ codeLength := by
        dsimp [header, codeLength, binaryTermFunctionHeaderCost]
        simp only [binaryTermCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hcodePos : 1 ≤ codeLength := by
        have := four_le_binaryTermCode_length
          (Semiterm.func functionSymbol arguments)
        dsimp [codeLength]
        omega
      have hrootCharge :
          2 * header + 3 + (4 * budget + 4) * codeLength ≤
            factor * codeLength := by
        calc
          2 * header + 3 + (4 * budget + 4) * codeLength ≤
              2 * codeLength + 3 * codeLength +
                (4 * budget + 4) * codeLength := by omega
          _ = (2 + 3 + (4 * budget + 4)) * codeLength := by
            simp only [Nat.add_mul]
          _ ≤ factor * codeLength :=
            Nat.mul_le_mul_right codeLength (by
              dsimp [factor]
              omega)
      simp only [binaryTermFvSupTrace, termSymbolCount]
      rw [Nat.mul_add, Nat.mul_one]
      dsimp [codeLength, symbols, factor, header, values] at hchildren' hmaximum hrootCharge ⊢
      omega

theorem binaryTermFvSupTrace_cost_le {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermFvSupTrace term).2 ≤
      100 * ((binaryTermCode term).length + 1) *
        (binaryTermCode term).length ^ 2 := by
  let codeLength := (binaryTermCode term).length
  have htrace := binaryTermFvSupTrace_cost_le_budget term
    codeLength le_rfl
  have hsymbols := termSymbolCount_le_binaryTermCode_length term
  have hscaled := Nat.mul_le_mul_left
    (100 * (codeLength + 1) * codeLength) hsymbols
  exact htrace.trans (by
    dsimp [codeLength] at htrace hscaled ⊢
    simpa [pow_two, Nat.mul_assoc] using hscaled)

theorem binaryFormulaFvSupTrace_cost_le_budget :
    ∀ {arity : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
      (budget : Nat),
      (binaryFormulaCode formula).length ≤ budget →
      (binaryFormulaFvSupTrace formula).2 ≤
        (500 * (budget + 1)) *
          (binaryFormulaCode formula).length *
          formulaSymbolCount formula
  | _, ⊤, budget, hbudget => by
      have hcode := two_le_binaryNatCode_length 2
      have hfactor : 5 ≤ 500 * (budget + 1) := by omega
      change
        2 * binaryFormulaNodeHeaderCost 2 + 3 ≤
          (500 * (budget + 1)) *
            (binaryFormulaNodeHeaderCost 2) * 1
      dsimp [binaryFormulaNodeHeaderCost]
      have hscaled := Nat.mul_le_mul_right
        (binaryNatCode 2).length hfactor
      omega
  | _, ⊥, budget, hbudget => by
      have hcode := two_le_binaryNatCode_length 3
      have hfactor : 5 ≤ 500 * (budget + 1) := by omega
      change
        2 * binaryFormulaNodeHeaderCost 3 + 3 ≤
          (500 * (budget + 1)) *
            (binaryFormulaNodeHeaderCost 3) * 1
      dsimp [binaryFormulaNodeHeaderCost]
      have hscaled := Nat.mul_le_mul_right
        (binaryNatCode 3).length hfactor
      omega
  | _, Semiformula.rel relationSymbol arguments, budget, hbudget => by
      rename_i relationArity
      let codeLength := (binaryFormulaCode
        (Semiformula.rel relationSymbol arguments)).length
      let symbols := formulaSymbolCount
        (Semiformula.rel relationSymbol arguments)
      let factor := 500 * (budget + 1)
      let header := binaryFormulaAtomHeaderCost 0 relationSymbol
      let values := Matrix.toList
        (fun index => (binaryTermFvSupTrace (arguments index)).1)
      have hchild (index : Fin _) :
          (binaryTermCode (arguments index)).length ≤ codeLength := by
        have hsingle :
            (binaryTermCode (arguments index)).length ≤
              Finset.univ.sum
                (fun child =>
                  (binaryTermCode (arguments child)).length) :=
          Finset.single_le_sum
            (fun child _ => Nat.zero_le
              (binaryTermCode (arguments child)).length)
            (Finset.mem_univ index)
        dsimp [codeLength, header, binaryFormulaAtomHeaderCost]
        simp only [binaryFormulaCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFvSupTrace (arguments index)).2) ≤
            factor * codeLength *
              Finset.univ.sum
                (fun index => termSymbolCount (arguments index)) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                factor * codeLength *
                  termSymbolCount (arguments index)) := by
            apply Finset.sum_le_sum
            intro index hindex
            have hterm := binaryTermFvSupTrace_cost_le_budget
              (arguments index) budget ((hchild index).trans hbudget)
            have hcoefficient :
                (100 * (budget + 1)) *
                    (binaryTermCode (arguments index)).length ≤
                  factor * codeLength := by
              exact Nat.mul_le_mul (by
                dsimp [factor]
                omega) (hchild index)
            exact hterm.trans
              (Nat.mul_le_mul_right
                (termSymbolCount (arguments index)) hcoefficient)
          _ = _ := by rw [Finset.mul_sum]
      have hvalues : ∀ value ∈ values,
          Nat.size value ≤ budget := by
        intro value hvalue
        rw [Matrix.mem_toList_iff] at hvalue
        rcases hvalue with ⟨index, hindex⟩
        rw [← hindex]
        exact (binaryTermFvSupTrace_size_le_code
          (arguments index)).trans ((hchild index).trans hbudget)
      have hmaximumRaw :=
        binaryNatMaxListTrace_cost_le values budget hvalues
      have harity : (List.ofFn arguments).length + 1 ≤ symbols := by
        have hsum : relationArity ≤
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index)) := by
          calc
            relationArity = Finset.univ.sum
                (fun _ : Fin relationArity => 1) := by
              simp
            _ ≤ Finset.univ.sum
                (fun index => termSymbolCount (arguments index)) :=
              Finset.sum_le_sum (fun index _ =>
                one_le_termSymbolCount (arguments index))
        have hlength : (List.ofFn arguments).length = relationArity := by
          simp
        dsimp [symbols]
        simp only [formulaSymbolCount]
        rw [hlength]
        omega
      have hsymbolsCode : symbols ≤ codeLength := by
        exact formulaSymbolCount_le_binaryFormulaCode_length
          (Semiformula.rel relationSymbol arguments)
      have hmaximum :
          (binaryNatMaxListTrace values).2 ≤
            (4 * budget + 4) * codeLength := by
        have hlength : values.length = (List.ofFn arguments).length := by
          simp [values]
        rw [hlength] at hmaximumRaw
        exact hmaximumRaw.trans
          (Nat.mul_le_mul_left (4 * budget + 4)
            (harity.trans hsymbolsCode))
      have hheaderCode : header ≤ codeLength := by
        dsimp [header, codeLength, binaryFormulaAtomHeaderCost]
        simp only [binaryFormulaCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hcodePos : 1 ≤ codeLength := by
        have := two_le_binaryNatCode_length 0
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hrootCharge :
          2 * header + 3 + (4 * budget + 4) * codeLength ≤
            factor * codeLength := by
        calc
          2 * header + 3 + (4 * budget + 4) * codeLength ≤
              2 * codeLength + 3 * codeLength +
                (4 * budget + 4) * codeLength := by omega
          _ = (2 + 3 + (4 * budget + 4)) * codeLength := by
            simp only [Nat.add_mul]
          _ ≤ factor * codeLength :=
            Nat.mul_le_mul_right codeLength (by
              dsimp [factor]
              omega)
      simp only [binaryFormulaFvSupTrace, formulaSymbolCount]
      rw [Nat.mul_add, Nat.mul_one]
      dsimp [codeLength, symbols, factor, header, values] at hchildren hmaximum hrootCharge ⊢
      omega
  | _, Semiformula.nrel relationSymbol arguments, budget, hbudget => by
      rename_i relationArity
      let codeLength := (binaryFormulaCode
        (Semiformula.nrel relationSymbol arguments)).length
      let symbols := formulaSymbolCount
        (Semiformula.nrel relationSymbol arguments)
      let factor := 500 * (budget + 1)
      let header := binaryFormulaAtomHeaderCost 1 relationSymbol
      let values := Matrix.toList
        (fun index => (binaryTermFvSupTrace (arguments index)).1)
      have hchild (index : Fin _) :
          (binaryTermCode (arguments index)).length ≤ codeLength := by
        have hsingle :
            (binaryTermCode (arguments index)).length ≤
              Finset.univ.sum
                (fun child =>
                  (binaryTermCode (arguments child)).length) :=
          Finset.single_le_sum
            (fun child _ => Nat.zero_le
              (binaryTermCode (arguments child)).length)
            (Finset.mem_univ index)
        dsimp [codeLength, header, binaryFormulaAtomHeaderCost]
        simp only [binaryFormulaCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFvSupTrace (arguments index)).2) ≤
            factor * codeLength *
              Finset.univ.sum
                (fun index => termSymbolCount (arguments index)) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                factor * codeLength *
                  termSymbolCount (arguments index)) := by
            apply Finset.sum_le_sum
            intro index hindex
            have hterm := binaryTermFvSupTrace_cost_le_budget
              (arguments index) budget ((hchild index).trans hbudget)
            have hcoefficient :
                (100 * (budget + 1)) *
                    (binaryTermCode (arguments index)).length ≤
                  factor * codeLength := by
              exact Nat.mul_le_mul (by
                dsimp [factor]
                omega) (hchild index)
            exact hterm.trans
              (Nat.mul_le_mul_right
                (termSymbolCount (arguments index)) hcoefficient)
          _ = _ := by rw [Finset.mul_sum]
      have hvalues : ∀ value ∈ values,
          Nat.size value ≤ budget := by
        intro value hvalue
        rw [Matrix.mem_toList_iff] at hvalue
        rcases hvalue with ⟨index, hindex⟩
        rw [← hindex]
        exact (binaryTermFvSupTrace_size_le_code
          (arguments index)).trans ((hchild index).trans hbudget)
      have hmaximumRaw :=
        binaryNatMaxListTrace_cost_le values budget hvalues
      have harity : (List.ofFn arguments).length + 1 ≤ symbols := by
        have hsum : relationArity ≤
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index)) := by
          calc
            relationArity = Finset.univ.sum
                (fun _ : Fin relationArity => 1) := by
              simp
            _ ≤ Finset.univ.sum
                (fun index => termSymbolCount (arguments index)) :=
              Finset.sum_le_sum (fun index _ =>
                one_le_termSymbolCount (arguments index))
        have hlength : (List.ofFn arguments).length = relationArity := by
          simp
        dsimp [symbols]
        simp only [formulaSymbolCount]
        rw [hlength]
        omega
      have hsymbolsCode : symbols ≤ codeLength := by
        exact formulaSymbolCount_le_binaryFormulaCode_length
          (Semiformula.nrel relationSymbol arguments)
      have hmaximum :
          (binaryNatMaxListTrace values).2 ≤
            (4 * budget + 4) * codeLength := by
        have hlength : values.length = (List.ofFn arguments).length := by
          simp [values]
        rw [hlength] at hmaximumRaw
        exact hmaximumRaw.trans
          (Nat.mul_le_mul_left (4 * budget + 4)
            (harity.trans hsymbolsCode))
      have hheaderCode : header ≤ codeLength := by
        dsimp [header, codeLength, binaryFormulaAtomHeaderCost]
        simp only [binaryFormulaCode, List.length_append]
        rw [length_flatten_ofFn]
        omega
      have hcodePos : 1 ≤ codeLength := by
        have := two_le_binaryNatCode_length 1
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hrootCharge :
          2 * header + 3 + (4 * budget + 4) * codeLength ≤
            factor * codeLength := by
        calc
          2 * header + 3 + (4 * budget + 4) * codeLength ≤
              2 * codeLength + 3 * codeLength +
                (4 * budget + 4) * codeLength := by omega
          _ = (2 + 3 + (4 * budget + 4)) * codeLength := by
            simp only [Nat.add_mul]
          _ ≤ factor * codeLength :=
            Nat.mul_le_mul_right codeLength (by
              dsimp [factor]
              omega)
      simp only [binaryFormulaFvSupTrace, formulaSymbolCount]
      rw [Nat.mul_add, Nat.mul_one]
      dsimp [codeLength, symbols, factor, header, values] at hchildren hmaximum hrootCharge ⊢
      omega
  | _, left ⋏ right, budget, hbudget => by
      let codeLength := (binaryFormulaCode (left ⋏ right)).length
      let factor := 500 * (budget + 1)
      have hleftCode : (binaryFormulaCode left).length ≤ codeLength := by
        have htag := two_le_binaryNatCode_length 4
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hrightCode : (binaryFormulaCode right).length ≤ codeLength := by
        have htag := two_le_binaryNatCode_length 4
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hleft := binaryFormulaFvSupTrace_cost_le_budget left budget
        (hleftCode.trans hbudget)
      have hright := binaryFormulaFvSupTrace_cost_le_budget right budget
        (hrightCode.trans hbudget)
      have hleft' :
          (binaryFormulaFvSupTrace left).2 ≤
            factor * codeLength * formulaSymbolCount left :=
        hleft.trans (Nat.mul_le_mul_right (formulaSymbolCount left)
          (Nat.mul_le_mul_left factor hleftCode))
      have hright' :
          (binaryFormulaFvSupTrace right).2 ≤
            factor * codeLength * formulaSymbolCount right :=
        hright.trans (Nat.mul_le_mul_right (formulaSymbolCount right)
          (Nat.mul_le_mul_left factor hrightCode))
      have hleftSize := (binaryFormulaFvSupTrace_size_le_code left).trans
        (hleftCode.trans hbudget)
      have hrightSize := (binaryFormulaFvSupTrace_size_le_code right).trans
        (hrightCode.trans hbudget)
      have hmaximumRaw := binaryNatMaxTrace_cost_le
        (binaryFormulaFvSupTrace left).1
        (binaryFormulaFvSupTrace right).1
      have hmaximum :
          (binaryNatMaxTrace
            (binaryFormulaFvSupTrace left).1
            (binaryFormulaFvSupTrace right).1).2 ≤
              4 * budget + 3 := hmaximumRaw.trans (by omega)
      have htag := two_le_binaryNatCode_length 4
      have hcodePos : 1 ≤ codeLength := by
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderCode :
          binaryFormulaNodeHeaderCost 4 ≤ codeLength := by
        dsimp [binaryFormulaNodeHeaderCost, codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderBudget :
          binaryFormulaNodeHeaderCost 4 ≤ budget :=
        hheaderCode.trans hbudget
      have hrootCharge :
          4 * budget + 3 + 2 * binaryFormulaNodeHeaderCost 4 + 3 ≤
            factor * codeLength := by
        have hbase :
            4 * budget + 3 + 2 * binaryFormulaNodeHeaderCost 4 + 3 ≤
              factor := by
          dsimp [factor]
          omega
        have hscaled := Nat.mul_le_mul_left factor hcodePos
        exact hbase.trans (by simpa using hscaled)
      simp only [binaryFormulaFvSupTrace, formulaSymbolCount]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      dsimp [factor, codeLength] at hleft' hright' hrootCharge ⊢
      omega
  | _, left ⋎ right, budget, hbudget => by
      let codeLength := (binaryFormulaCode (left ⋎ right)).length
      let factor := 500 * (budget + 1)
      have hleftCode : (binaryFormulaCode left).length ≤ codeLength := by
        have htag := two_le_binaryNatCode_length 5
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hrightCode : (binaryFormulaCode right).length ≤ codeLength := by
        have htag := two_le_binaryNatCode_length 5
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hleft := binaryFormulaFvSupTrace_cost_le_budget left budget
        (hleftCode.trans hbudget)
      have hright := binaryFormulaFvSupTrace_cost_le_budget right budget
        (hrightCode.trans hbudget)
      have hleft' :
          (binaryFormulaFvSupTrace left).2 ≤
            factor * codeLength * formulaSymbolCount left :=
        hleft.trans (Nat.mul_le_mul_right (formulaSymbolCount left)
          (Nat.mul_le_mul_left factor hleftCode))
      have hright' :
          (binaryFormulaFvSupTrace right).2 ≤
            factor * codeLength * formulaSymbolCount right :=
        hright.trans (Nat.mul_le_mul_right (formulaSymbolCount right)
          (Nat.mul_le_mul_left factor hrightCode))
      have hleftSize := (binaryFormulaFvSupTrace_size_le_code left).trans
        (hleftCode.trans hbudget)
      have hrightSize := (binaryFormulaFvSupTrace_size_le_code right).trans
        (hrightCode.trans hbudget)
      have hmaximumRaw := binaryNatMaxTrace_cost_le
        (binaryFormulaFvSupTrace left).1
        (binaryFormulaFvSupTrace right).1
      have hmaximum :
          (binaryNatMaxTrace
            (binaryFormulaFvSupTrace left).1
            (binaryFormulaFvSupTrace right).1).2 ≤
              4 * budget + 3 := hmaximumRaw.trans (by omega)
      have htag := two_le_binaryNatCode_length 5
      have hcodePos : 1 ≤ codeLength := by
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderCode :
          binaryFormulaNodeHeaderCost 5 ≤ codeLength := by
        dsimp [binaryFormulaNodeHeaderCost, codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderBudget :
          binaryFormulaNodeHeaderCost 5 ≤ budget :=
        hheaderCode.trans hbudget
      have hrootCharge :
          4 * budget + 3 + 2 * binaryFormulaNodeHeaderCost 5 + 3 ≤
            factor * codeLength := by
        have hbase :
            4 * budget + 3 + 2 * binaryFormulaNodeHeaderCost 5 + 3 ≤
              factor := by
          dsimp [factor]
          omega
        have hscaled := Nat.mul_le_mul_left factor hcodePos
        exact hbase.trans (by simpa using hscaled)
      simp only [binaryFormulaFvSupTrace, formulaSymbolCount]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      dsimp [factor, codeLength] at hleft' hright' hrootCharge ⊢
      omega
  | _, ∀⁰ body, budget, hbudget => by
      let codeLength := (binaryFormulaCode (∀⁰ body)).length
      let factor := 500 * (budget + 1)
      have hbodyCode : (binaryFormulaCode body).length ≤ codeLength := by
        have htag := two_le_binaryNatCode_length 6
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hbody := binaryFormulaFvSupTrace_cost_le_budget body budget
        (hbodyCode.trans hbudget)
      have hbody' :
          (binaryFormulaFvSupTrace body).2 ≤
            factor * codeLength * formulaSymbolCount body :=
        hbody.trans (Nat.mul_le_mul_right (formulaSymbolCount body)
          (Nat.mul_le_mul_left factor hbodyCode))
      have htag := two_le_binaryNatCode_length 6
      have hcodePos : 1 ≤ codeLength := by
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderCode :
          binaryFormulaNodeHeaderCost 6 ≤ codeLength := by
        dsimp [binaryFormulaNodeHeaderCost, codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderBudget :
          binaryFormulaNodeHeaderCost 6 ≤ budget :=
        hheaderCode.trans hbudget
      have hrootCharge :
          2 * binaryFormulaNodeHeaderCost 6 + 3 ≤
            factor * codeLength := by
        have hbase :
            2 * binaryFormulaNodeHeaderCost 6 + 3 ≤ factor := by
          dsimp [factor]
          omega
        have hscaled := Nat.mul_le_mul_left factor hcodePos
        exact hbase.trans (by simpa using hscaled)
      simp only [binaryFormulaFvSupTrace, formulaSymbolCount]
      rw [Nat.mul_add, Nat.mul_one]
      dsimp [factor, codeLength] at hbody' hrootCharge ⊢
      omega
  | _, ∃⁰ body, budget, hbudget => by
      let codeLength := (binaryFormulaCode (∃⁰ body)).length
      let factor := 500 * (budget + 1)
      have hbodyCode : (binaryFormulaCode body).length ≤ codeLength := by
        have htag := two_le_binaryNatCode_length 7
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hbody := binaryFormulaFvSupTrace_cost_le_budget body budget
        (hbodyCode.trans hbudget)
      have hbody' :
          (binaryFormulaFvSupTrace body).2 ≤
            factor * codeLength * formulaSymbolCount body :=
        hbody.trans (Nat.mul_le_mul_right (formulaSymbolCount body)
          (Nat.mul_le_mul_left factor hbodyCode))
      have htag := two_le_binaryNatCode_length 7
      have hcodePos : 1 ≤ codeLength := by
        dsimp [codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderCode :
          binaryFormulaNodeHeaderCost 7 ≤ codeLength := by
        dsimp [binaryFormulaNodeHeaderCost, codeLength]
        simp only [binaryFormulaCode, List.length_append]
        omega
      have hheaderBudget :
          binaryFormulaNodeHeaderCost 7 ≤ budget :=
        hheaderCode.trans hbudget
      have hrootCharge :
          2 * binaryFormulaNodeHeaderCost 7 + 3 ≤
            factor * codeLength := by
        have hbase :
            2 * binaryFormulaNodeHeaderCost 7 + 3 ≤ factor := by
          dsimp [factor]
          omega
        have hscaled := Nat.mul_le_mul_left factor hcodePos
        exact hbase.trans (by simpa using hscaled)
      simp only [binaryFormulaFvSupTrace, formulaSymbolCount]
      rw [Nat.mul_add, Nat.mul_one]
      dsimp [factor, codeLength] at hbody' hrootCharge ⊢
      omega

theorem binaryFormulaFvSupTrace_cost_le {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaFvSupTrace formula).2 ≤
      500 * ((binaryFormulaCode formula).length + 1) *
        (binaryFormulaCode formula).length ^ 2 := by
  let codeLength := (binaryFormulaCode formula).length
  have htrace := binaryFormulaFvSupTrace_cost_le_budget formula
    codeLength le_rfl
  have hsymbols := formulaSymbolCount_le_binaryFormulaCode_length formula
  have hscaled := Nat.mul_le_mul_left
    (500 * (codeLength + 1) * codeLength) hsymbols
  exact htrace.trans (by
    dsimp [codeLength] at htrace hscaled ⊢
    simpa [pow_two, Nat.mul_assoc] using hscaled)

/-! ## One-pass execution of `Rew.fixitr`

The index trace follows the recursion of `fixitr`: each iteration captures
the current free variable zero, while a successor free index is passed to the
previous iteration.  Thus it performs `m` charged index steps without making
`m` complete passes over the surrounding syntax tree.
-/

def FixitrIndexSpec (m x : Nat) : Fin m ⊕ Nat → Prop
  | .inl index => index.val = x
  | .inr remainder => m ≤ x ∧ remainder = x - m

def binaryFixitrIndexTrace :
    (m x : Nat) → SyntaxTrace (Fin m ⊕ Nat)
  | 0, x =>
      (.inr x, (binaryNatCode x).length + 3)
  | m + 1, 0 =>
      (.inl 0, (binaryNatCode 0).length + 3)
  | m + 1, x + 1 =>
      let previous := binaryFixitrIndexTrace m x
      match previous.1 with
      | .inl index =>
          (.inl index.succ,
            previous.2 + (binaryNatCode (x + 1)).length + 3)
      | .inr remainder =>
          (.inr remainder,
            previous.2 + (binaryNatCode (x + 1)).length + 3)

theorem binaryFixitrIndexTrace_result :
    ∀ (m x : Nat),
      FixitrIndexSpec m x (binaryFixitrIndexTrace m x).1
  | 0, x => by simp [binaryFixitrIndexTrace, FixitrIndexSpec]
  | m + 1, 0 => by simp [binaryFixitrIndexTrace, FixitrIndexSpec]
  | m + 1, x + 1 => by
      have ih := binaryFixitrIndexTrace_result m x
      simp only [binaryFixitrIndexTrace]
      generalize htrace : binaryFixitrIndexTrace m x = trace at ih
      rcases trace with ⟨index, cost⟩
      cases index with
      | inl index =>
          simp only [FixitrIndexSpec, Fin.val_succ] at ih ⊢
          omega
      | inr remainder =>
          simp only [FixitrIndexSpec] at ih ⊢
          omega

theorem binaryFixitrIndexTrace_cost_le :
    ∀ (m x : Nat),
      (binaryFixitrIndexTrace m x).2 ≤
        (m + 1) * ((binaryNatCode x).length + 3)
  | 0, x => by simp [binaryFixitrIndexTrace]
  | m + 1, 0 => by
      simp [binaryFixitrIndexTrace]
  | m + 1, x + 1 => by
      have ih := binaryFixitrIndexTrace_cost_le m x
      have hmono :=
        FoundationCompactCanonicalDecodeLength.binaryNatCode_length_mono
          (Nat.le_succ x)
      have hstep :
          (binaryFixitrIndexTrace m x).2 ≤
            (m + 1) * ((binaryNatCode (x + 1)).length + 3) :=
        ih.trans (Nat.mul_le_mul_left (m + 1)
          (Nat.add_le_add_right hmono 3))
      have hadd := Nat.add_le_add_right hstep
        ((binaryNatCode (x + 1)).length + 3)
      simp only [binaryFixitrIndexTrace]
      generalize htrace : binaryFixitrIndexTrace m x = trace at hadd
      rcases trace with ⟨index, cost⟩
      cases index <;> simp only
      all_goals
        rw [Nat.add_mul]
        simpa [Nat.add_assoc] using hadd

def binaryTermFixitrTrace (m : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 →
      SyntaxTrace (LO.FirstOrder.ArithmeticSemiterm Nat (0 + m))
  | #index => Fin.elim0 index
  | term@(&x) =>
      let indexTrace := binaryFixitrIndexTrace m x
      match indexTrace.1 with
      | .inl index =>
          let output :=
            (#(Fin.cast (Nat.zero_add m).symm index) :
              LO.FirstOrder.ArithmeticSemiterm Nat (0 + m))
          (output, indexTrace.2 +
            (binaryTermCode term).length +
            (binaryTermCode output).length + 3)
      | .inr remainder =>
          let output :=
            (&remainder :
              LO.FirstOrder.ArithmeticSemiterm Nat (0 + m))
          (output, indexTrace.2 +
            (binaryTermCode term).length +
            (binaryTermCode output).length + 3)
  | Semiterm.func functionSymbol arguments =>
      let traces := fun index =>
        binaryTermFixitrTrace m (arguments index)
      (Semiterm.func functionSymbol (fun index => (traces index).1),
        2 * binaryTermFunctionHeaderCost functionSymbol + 3 +
          Finset.univ.sum (fun index => (traces index).2))

theorem binaryTermFixitrTrace_result (m : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermFixitrTrace m term).1 = Rew.fixitr 0 m term := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar x =>
      have hspec := binaryFixitrIndexTrace_result m x
      simp only [binaryTermFixitrTrace]
      generalize htrace : binaryFixitrIndexTrace m x = trace at hspec ⊢
      rcases trace with ⟨index, cost⟩
      cases index with
      | inl index =>
          simp only [Prod.fst]
          simp only [FixitrIndexSpec] at hspec
          have hx : x < m := by
            rw [← hspec]
            exact index.isLt
          rw [Rew.fixitr_fvar, dif_pos hx]
          congr
          apply Fin.ext
          simpa using hspec
      | inr remainder =>
          simp only [Prod.fst]
          simp only [FixitrIndexSpec] at hspec
          have hx : ¬x < m := Nat.not_lt.mpr hspec.1
          rw [Rew.fixitr_fvar, dif_neg hx]
          exact congrArg Semiterm.fvar hspec.2
  | func functionSymbol arguments ih =>
      simp only [binaryTermFixitrTrace, Rew.func]
      congr
      funext index
      exact ih index

theorem binaryTermFixitrTrace_code_length_le (m : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermCode (binaryTermFixitrTrace m term).1).length ≤
      (binaryTermCode term).length := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar x =>
      have hspec := binaryFixitrIndexTrace_result m x
      simp only [binaryTermFixitrTrace]
      generalize htrace : binaryFixitrIndexTrace m x = trace at hspec ⊢
      rcases trace with ⟨index, cost⟩
      cases index with
      | inl index =>
          simp only [FixitrIndexSpec] at hspec
          have hcastval :
              (Fin.cast (Nat.zero_add m).symm index).val = index.val := rfl
          simp only [binaryTermCode, List.length_append]
          rw [hcastval]
          rw [hspec]
          have htag0 := two_le_binaryNatCode_length 0
          have htag1 := two_le_binaryNatCode_length 1
          simp [binaryNatCode] at htag0 htag1 ⊢
      | inr remainder =>
          simp only [FixitrIndexSpec] at hspec
          have hmono :=
            FoundationCompactCanonicalDecodeLength.binaryNatCode_length_mono
              (show remainder ≤ x by omega)
          simp only [binaryTermCode, List.length_append]
          omega
  | func functionSymbol arguments ih =>
      simp only [binaryTermFixitrTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren := Finset.sum_le_sum
        (s := Finset.univ) (fun index _ => ih index)
      omega

theorem binaryTermFixitrTrace_cost_le (m : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermFixitrTrace m term).2 ≤
      32 * (m + 1) * (binaryTermCode term).length := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar x =>
      let input :=
        (&x : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      have hindex := binaryFixitrIndexTrace_cost_le m x
      have hcode := binaryTermFixitrTrace_code_length_le m input
      have hinput := four_le_binaryTermCode_length input
      have hnat :
          (binaryNatCode x).length + 3 ≤
            2 * (binaryTermCode input).length := by
        dsimp [input]
        simp only [binaryTermCode, List.length_append]
        have htag := two_le_binaryNatCode_length 1
        omega
      have hindex' :
          (binaryFixitrIndexTrace m x).2 ≤
            2 * (m + 1) * (binaryTermCode input).length :=
        hindex.trans (by
          have hscaled := Nat.mul_le_mul_left (m + 1) hnat
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled)
      dsimp [input] at hcode hinput
      simp only [binaryTermFixitrTrace] at hcode
      have hleaf :
          ∀ (output : LO.FirstOrder.ArithmeticSemiterm Nat (0 + m))
            (cost : Nat),
            cost ≤
                2 * (m + 1) * (binaryTermCode input).length →
            (binaryTermCode output).length ≤
                (binaryTermCode input).length →
            cost + (binaryTermCode input).length +
                (binaryTermCode output).length + 3 ≤
              32 * (m + 1) * (binaryTermCode input).length := by
        intro output cost hcost houtput
        let base := (m + 1) * (binaryTermCode input).length
        have hone : 1 ≤ m + 1 := by omega
        have hinputScale :
            (binaryTermCode input).length ≤ base := by
          have hscaled := Nat.mul_le_mul_right
            (binaryTermCode input).length hone
          simpa [base] using hscaled
        have houtputScale :
            (binaryTermCode output).length ≤ base :=
          houtput.trans hinputScale
        have hthreeScale : 3 ≤ base := by
          have hthree : 3 ≤ (binaryTermCode input).length := by
            have hthreeFour : 3 ≤ 4 := by omega
            exact hthreeFour.trans (by simpa [input] using hinput)
          exact hthree.trans hinputScale
        have hcostScale : cost ≤ 2 * base := by
          simpa [base, Nat.mul_assoc] using hcost
        calc
          cost + (binaryTermCode input).length +
                (binaryTermCode output).length + 3
              ≤ 2 * base + base + base + base := by omega
          _ ≤ 32 * base := by omega
          _ = 32 * (m + 1) * (binaryTermCode input).length := by
            simp [base, Nat.mul_assoc]
      simp only [binaryTermFixitrTrace]
      generalize htrace : binaryFixitrIndexTrace m x = trace at hindex' hcode ⊢
      rcases trace with ⟨index, cost⟩
      cases index with
      | inl index =>
          simp only at hcode hindex' ⊢
          exact hleaf _ _ hindex' hcode
      | inr remainder =>
          simp only at hcode hindex' ⊢
          exact hleaf _ _ hindex' hcode
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermFixitrTrace m (arguments index)).2) ≤
            32 * (m + 1) *
              Finset.univ.sum
                (fun index =>
                  (binaryTermCode (arguments index)).length) := by
        calc
          _ ≤ Finset.univ.sum
              (fun index =>
                32 * (m + 1) *
                  (binaryTermCode (arguments index)).length) :=
            Finset.sum_le_sum (fun index _ => ih index)
          _ = _ := by rw [Finset.mul_sum]
      have hheader : 1 ≤ binaryTermFunctionHeaderCost functionSymbol := by
        have htag := two_le_binaryNatCode_length 2
        dsimp [binaryTermFunctionHeaderCost]
        omega
      have hfactor : 5 ≤ 32 * (m + 1) := by omega
      have hcharge :
          2 * binaryTermFunctionHeaderCost functionSymbol + 3 ≤
            32 * (m + 1) *
              binaryTermFunctionHeaderCost functionSymbol := by
        have hscaled := Nat.mul_le_mul_right
          (binaryTermFunctionHeaderCost functionSymbol) hfactor
        omega
      simp only [binaryTermFixitrTrace, binaryTermCode,
        List.length_append]
      rw [length_flatten_ofFn, Nat.mul_add]
      dsimp [binaryTermFunctionHeaderCost] at hchildren hcharge ⊢
      omega

/-! ## Iterated universal closure

The trace follows `allClosure`'s dependent recursion.  Each recursive step
allocates and emits one universal node; it never treats the whole closure as
a unit-cost constructor.
-/

def binaryAllClosureTrace :
    {arity : Nat} →
      LO.FirstOrder.ArithmeticSemiformula Nat arity →
        SyntaxTrace LO.FirstOrder.ArithmeticProposition
  | 0, formula => (formula, 1)
  | arity + 1, formula =>
      let previous := binaryAllClosureTrace (∀⁰ formula)
      (previous.1,
        previous.2 + 2 * binaryFormulaNodeHeaderCost 6 + 3)

theorem binaryAllClosureTrace_result :
    ∀ {arity : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity),
      (binaryAllClosureTrace formula).1 = ∀⁰* formula
  | 0, formula => rfl
  | arity + 1, formula => by
      simp only [binaryAllClosureTrace, allClosure_succ]
      exact binaryAllClosureTrace_result (∀⁰ formula)

theorem binaryAllClosureTrace_cost_eq :
    ∀ {arity : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity),
      (binaryAllClosureTrace formula).2 =
        arity * (2 * binaryFormulaNodeHeaderCost 6 + 3) + 1
  | 0, formula => by simp [binaryAllClosureTrace]
  | arity + 1, formula => by
      simp only [binaryAllClosureTrace]
      rw [binaryAllClosureTrace_cost_eq (∀⁰ formula)]
      rw [Nat.add_mul]
      omega

theorem binaryAllClosureTrace_cost_le
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryAllClosureTrace formula).2 ≤ 24 * (arity + 1) := by
  rw [binaryAllClosureTrace_cost_eq]
  have hheader : binaryFormulaNodeHeaderCost 6 = 8 := by decide
  rw [hheader]
  omega

theorem binaryAllClosureTrace_code_length_eq :
    ∀ {arity : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity),
      (binaryFormulaCode (binaryAllClosureTrace formula).1).length =
        arity * (binaryNatCode 6).length +
          (binaryFormulaCode formula).length
  | 0, formula => by simp [binaryAllClosureTrace]
  | arity + 1, formula => by
      simp only [binaryAllClosureTrace]
      rw [binaryAllClosureTrace_code_length_eq (∀⁰ formula)]
      simp only [binaryFormulaCode, List.length_append]
      rw [Nat.add_mul]
      omega

#print axioms binaryTermShiftTrace_result
#print axioms binaryTermShiftTrace_cost_le
#print axioms binaryFormulaShiftTrace_result
#print axioms binaryFormulaShiftTrace_cost_le
#print axioms binaryFormulaFreeTrace_result
#print axioms binaryFormulaFreeTrace_cost_le
#print axioms formulaListShiftTrace_result
#print axioms formulaListShiftTrace_cost_le
#print axioms binaryFormulaRewTrace_result
#print axioms binaryBitsCompareTrace_natBits_result
#print axioms binaryNatCompareTrace_result
#print axioms binaryNatCompareTrace_cost_le
#print axioms binaryNatLeTrace_result_eq_true_iff
#print axioms binaryNatLeTrace_cost_le
#print axioms binaryNatMaxTrace_result
#print axioms binaryNatMaxTrace_cost_le
#print axioms binaryNatMaxListTrace_result
#print axioms binaryNatMaxListTrace_cost_le
#print axioms binaryTermFvSupTrace_result
#print axioms binaryFormulaFvSupTrace_result
#print axioms binaryTermFvSupTrace_size_le_code
#print axioms binaryFormulaFvSupTrace_size_le_code
#print axioms binaryTermFvSupTrace_cost_le
#print axioms binaryFormulaFvSupTrace_cost_le
#print axioms binaryFixitrIndexTrace_result
#print axioms binaryFixitrIndexTrace_cost_le
#print axioms binaryTermFixitrTrace_result
#print axioms binaryTermFixitrTrace_code_length_le
#print axioms binaryTermFixitrTrace_cost_le
#print axioms binaryAllClosureTrace_result
#print axioms binaryAllClosureTrace_cost_eq
#print axioms binaryAllClosureTrace_cost_le
#print axioms binaryAllClosureTrace_code_length_eq

end FoundationCompactSyntaxTransformationTraceCore
