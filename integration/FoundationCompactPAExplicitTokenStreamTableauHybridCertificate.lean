import integration.FoundationCompactNumericListedDirectCanonicalTokenStreamExplicitInput
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAFixedWidthEntryHybridCompiler
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactPATokenSegmentExplicitHybridCertificate

/-!
# Fully explicit hybrid certificate for a token-stream tableau

Every tableau row is supplied by `ExplicitTokenStreamTableauInput`.  The
bounded universal is assembled from concrete branches, and each row installs
its token, offset, and next-offset witnesses directly.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExplicitTokenStreamTableauHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectCanonicalTokenStreamExplicitInput
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAFixedWidthEntryHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPATokenSegmentExplicitHybridCertificate
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private abbrev HybridBranches
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bound : Nat) :=
  CheckedHybridValuationUniversalBranches valuation body bound

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_emptyFormulaSubstitution
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity Nat targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm Empty sourceArity) :
    rewriting ▹ (formula ⇜ terms) =
      (Rewriting.emb (ξ := Nat) formula) ⇜ (rewriting ∘ terms) := by
  have hcomposition :
      rewriting.comp (Rew.subst terms) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ (formula ⇜ terms) =
        (rewriting.comp (Rew.subst terms)) ▹ formula := by
      rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity)) ▹
        formula := by rw [hcomposition]
    _ = (Rewriting.emb (ξ := Nat) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rew_comp_assoc
    {ξ₁ ξ₂ ξ₃ ξ₄ : Type*} {n₁ n₂ n₃ n₄ : Nat}
    (third : Rew ℒₒᵣ ξ₃ n₃ ξ₄ n₄)
    (second : Rew ℒₒᵣ ξ₂ n₂ ξ₃ n₃)
    (first : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) :
    (third.comp second).comp first = third.comp (second.comp first) := by
  ext coordinate <;> simp [Rew.comp_app]

private theorem subst_bShiftTerm
    (term witness : ValuationTerm) :
    Rew.subst ![witness] (Rew.bShift term) = term := by
  calc
    Rew.subst ![witness] (Rew.bShift term) =
        ((Rew.subst ![witness]).comp Rew.bShift) term := by
      rw [Rew.comp_app]
    _ = Rew.id term := by rw [Rew.subst_comp_bShift_eq_id]
    _ = term := Rew.id_app term

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation
      (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_shortBinaryNumeralAddOne
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation
        (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm) =
      value + 1 := by
  rw [termValue_arithmeticAdd, termValue_shortBinaryNumeralTerm,
    termValue_arithmeticOne]

private theorem rewrite_bShift2_shortBinaryNumeralTerm
    (rewriting : Rew ℒₒᵣ Nat 2 Nat 0) (value : Nat) :
    rewriting
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      shortBinaryNumeralTerm value := by
  let composite := (rewriting.comp Rew.bShift).comp Rew.bShift
  have h := LO.FirstOrder.Semiterm.rew_eq_of_funEqOn composite Rew.id
    (shortBinaryNumeralTerm value)
    (fun index => Fin.elim0 index)
    (fun index hindex => by
      have : index ∈ (shortBinaryNumeralTerm value).freeVariables := hindex
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [composite, Rew.comp_app] using h

private theorem rewrite_bShift3_shortBinaryNumeralTerm
    (rewriting : Rew ℒₒᵣ Nat 3 Nat 0) (value : Nat) :
    rewriting
        (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))) =
      shortBinaryNumeralTerm value := by
  let composite := ((rewriting.comp Rew.bShift).comp Rew.bShift).comp
    Rew.bShift
  have h := LO.FirstOrder.Semiterm.rew_eq_of_funEqOn composite Rew.id
    (shortBinaryNumeralTerm value)
    (fun index => Fin.elim0 index)
    (fun index hindex => by
      have : index ∈ (shortBinaryNumeralTerm value).freeVariables := hindex
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [composite, Rew.comp_app] using h

private theorem rewrite_bShift4_shortBinaryNumeralTerm
    (rewriting : Rew ℒₒᵣ Nat 4 Nat 0) (value : Nat) :
    rewriting
        (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value))))) =
      shortBinaryNumeralTerm value := by
  let composite := (((rewriting.comp Rew.bShift).comp Rew.bShift).comp
    Rew.bShift).comp Rew.bShift
  have h := LO.FirstOrder.Semiterm.rew_eq_of_funEqOn composite Rew.id
    (shortBinaryNumeralTerm value)
    (fun index => Fin.elim0 index)
    (fun index hindex => by
      have : index ∈ (shortBinaryNumeralTerm value).freeVariables := hindex
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [composite, Rew.comp_app] using h

@[simp] private theorem free_bvar_one_fin2 :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 1)) (#(Fin.last 1)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_one_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) = #1 := by
  change (Rew.free (L := ℒₒᵣ) (n := 2))
    (#(Fin.castSucc (1 : Fin 2))) = #1
  exact Rew.free_bvar_castSucc 1

@[simp] private theorem free_bvar_two_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 2)) (#(Fin.last 2)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_one_fin4 :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 4) = #1 := by
  change (Rew.free (L := ℒₒᵣ) (n := 3))
    (#(Fin.castSucc (1 : Fin 3))) = #1
  exact Rew.free_bvar_castSucc 1

@[simp] private theorem free_bvar_two_fin4 :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 4) = #2 := by
  change (Rew.free (L := ℒₒᵣ) (n := 3))
    (#(Fin.castSucc (2 : Fin 3))) = #2
  exact Rew.free_bvar_castSucc 2

@[simp] private theorem free_bvar_three_fin4 :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (#3 : LO.FirstOrder.ArithmeticSemiterm Nat 4) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 3)) (#(Fin.last 3)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem q_bvar_one
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 1 targetVariables targetArity) :
    rewriting.q (#1 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 2) =
      Rew.bShift (rewriting #0) := by
  change rewriting.q (#((0 : Fin 1).succ)) = Rew.bShift (rewriting #0)
  exact Rew.q_bvar_succ rewriting 0

@[simp] private theorem q_bvar_two
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 2 targetVariables targetArity) :
    rewriting.q (#2 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 3) =
      Rew.bShift (rewriting #1) := by
  change rewriting.q (#((1 : Fin 2).succ)) = Rew.bShift (rewriting #1)
  exact Rew.q_bvar_succ rewriting 1

@[simp] private theorem q_bvar_one_fin3
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 2 targetVariables targetArity) :
    rewriting.q (#1 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 3) =
      Rew.bShift (rewriting #0) := by
  change rewriting.q (#((0 : Fin 2).succ)) = Rew.bShift (rewriting #0)
  exact Rew.q_bvar_succ rewriting 0

@[simp] private theorem q_bvar_three
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 3 targetVariables targetArity) :
    rewriting.q (#3 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 4) =
      Rew.bShift (rewriting #2) := by
  change rewriting.q (#((2 : Fin 3).succ)) = Rew.bShift (rewriting #2)
  exact Rew.q_bvar_succ rewriting 2

private def tableauOuterTerms
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Fin 6 -> ValuationTerm :=
  ![shortBinaryNumeralTerm payload,
    shortBinaryNumeralTerm payloadLength,
    shortBinaryNumeralTerm sentinel,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm offsetTable]

private theorem tableauOuterRewriting_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.subst (tableauOuterTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)).comp
        (Rew.emb : Rew ℒₒᵣ Empty 6 Nat 6) =
      Rew.embSubsts (tableauOuterTerms payload payloadLength sentinel tokenCount
        tokenTable offsetTable) := by
  ext coordinate
  · simp [Rew.comp_app]
  · exact Empty.elim coordinate

/-- The six public coordinates of the quoted tableau predicate, all installed
as short binary numerals. -/
def compactBinaryNatTokenStreamTableauClosedFormula
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat) compactBinaryNatTokenStreamTableauDef.val) ⇜
    tableauOuterTerms payload payloadLength sentinel tokenCount tokenTable
      offsetTable

/-- Public expansion of the six closed coordinates.  Downstream formula
alignment proofs can use this theorem without unfolding the private term
vector representation. -/
theorem compactBinaryNatTokenStreamTableauClosedFormula_identity
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    compactBinaryNatTokenStreamTableauClosedFormula payload payloadLength
        sentinel tokenCount tokenTable offsetTable =
      (Rewriting.emb (ξ := Nat)
          compactBinaryNatTokenStreamTableauDef.val) ⇜
        ![shortBinaryNumeralTerm payload,
          shortBinaryNumeralTerm payloadLength,
          shortBinaryNumeralTerm sentinel,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm offsetTable] := by
  rfl

private def shift4 (term : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiterm Nat 4 :=
  Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift term)))

private def tableauSourceRowCore :
    LO.FirstOrder.ArithmeticSemiformula Empty 10 :=
  (compactFixedWidthEntryDef.val ⇜ ![#8, #5, #3, #2]) ⋏
    ((compactFixedWidthEntryDef.val ⇜ ![#9, #5, #3, #1]) ⋏
      ((compactFixedWidthEntryDef.val ⇜ ![#9, #5, (‘#3 + 1’), #0]) ⋏
        (compactBinaryNatTokenSegmentDef.val ⇜ ![#4, #1, #2, #0])))

private def tableauSourceNextBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 10 :=
  “#0 < #6 + 1” ⋏ tableauSourceRowCore

private def tableauSourceOffsetBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 9 :=
  “#0 < #5 + 1” ⋏ (∃⁰ tableauSourceNextBody)

private def tableauSourceTokenBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 8 :=
  “#0 < #4 + 1” ⋏ (∃⁰ tableauSourceOffsetBody)

private def tableauSourceRowBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 7 :=
  ∃⁰ tableauSourceTokenBody

private def tableauSourceUniversalFormula :
    LO.FirstOrder.ArithmeticSemiformula Empty 6 :=
  (((tableauSourceRowCore.bexsLTSucc
      (#5 : LO.FirstOrder.ArithmeticSemiterm Empty 9)).bexsLTSucc
    (#4 : LO.FirstOrder.ArithmeticSemiterm Empty 8)).bexsLTSucc
      (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 7)).ballLT
    (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 6)

private def tableauSourceZeroTerm :
    LO.FirstOrder.ArithmeticSemiterm Empty 6 :=
  ‘0’

private def tableauSourceDecomposedFormula :
    LO.FirstOrder.ArithmeticSemiformula Empty 6 :=
  (expDef.val ⇜ ![#2, #1]) ⋏
    (“#3 ≤ #1 + 1” ⋏
      ((compactFixedWidthEntryDef.val ⇜
          ![#5, #1, tableauSourceZeroTerm, tableauSourceZeroTerm]) ⋏
        ((compactFixedWidthEntryDef.val ⇜ ![#5, #1, #3, #1]) ⋏
          tableauSourceUniversalFormula)))

private theorem compactBinaryNatTokenStreamTableauDef_val_eq_sourceDecomposed :
    compactBinaryNatTokenStreamTableauDef.val =
      tableauSourceDecomposedFormula := by
  unfold compactBinaryNatTokenStreamTableauDef
  unfold tableauSourceDecomposedFormula tableauSourceUniversalFormula
  unfold tableauSourceZeroTerm
  unfold tableauSourceRowCore
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq,
    Rew.func, Matrix.empty_eq]

private def tableauDepthOneTerms
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Fin 7 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![#0, Rew.bShift (shortBinaryNumeralTerm payload),
    Rew.bShift (shortBinaryNumeralTerm payloadLength),
    Rew.bShift (shortBinaryNumeralTerm sentinel),
    Rew.bShift (shortBinaryNumeralTerm tokenCount),
    Rew.bShift (shortBinaryNumeralTerm tokenTable),
    Rew.bShift (shortBinaryNumeralTerm offsetTable)]

private def tableauDepthTwoTerms
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Fin 8 -> LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
  ![#0, #1, Rew.bShift (Rew.bShift (shortBinaryNumeralTerm payload)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm payloadLength)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sentinel)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm tokenCount)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm tokenTable)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm offsetTable))]

private def tableauDepthThreeTerms
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Fin 9 -> LO.FirstOrder.ArithmeticSemiterm Nat 3 :=
  ![#0, #1, #2,
    Rew.bShift (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm payload))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm payloadLength))),
    Rew.bShift (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sentinel))),
    Rew.bShift (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm tokenCount))),
    Rew.bShift (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm tokenTable))),
    Rew.bShift (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm offsetTable)))]

private def tableauDepthFourTerms
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Fin 10 -> LO.FirstOrder.ArithmeticSemiterm Nat 4 :=
  ![#0, #1, #2, #3,
    shift4 (shortBinaryNumeralTerm payload),
    shift4 (shortBinaryNumeralTerm payloadLength),
    shift4 (shortBinaryNumeralTerm sentinel),
    shift4 (shortBinaryNumeralTerm tokenCount),
    shift4 (shortBinaryNumeralTerm tokenTable),
    shift4 (shortBinaryNumeralTerm offsetTable)]

private theorem tableauOuterQ1_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.embSubsts (tableauOuterTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)).q =
      Rew.embSubsts (tableauDepthOneTerms payload payloadLength sentinel
        tokenCount tokenTable offsetTable) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [tableauOuterTerms, tableauDepthOneTerms, Rew.q]
  · exact Empty.elim coordinate

private theorem tableauOuterQ2_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.embSubsts (tableauOuterTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)).q.q =
      Rew.embSubsts (tableauDepthTwoTerms payload payloadLength sentinel
        tokenCount tokenTable offsetTable) := by
  rw [tableauOuterQ1_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [tableauDepthOneTerms, tableauDepthTwoTerms, Rew.q]
  · exact Empty.elim coordinate

private theorem tableauDepthOneQ_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.embSubsts (tableauDepthOneTerms payload payloadLength sentinel
      tokenCount tokenTable offsetTable)).q =
      Rew.embSubsts (tableauDepthTwoTerms payload payloadLength sentinel
        tokenCount tokenTable offsetTable) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [tableauDepthOneTerms, tableauDepthTwoTerms, Rew.q]
  · exact Empty.elim coordinate

private theorem tableauOuterQ3_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.embSubsts (tableauOuterTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)).q.q.q =
      Rew.embSubsts (tableauDepthThreeTerms payload payloadLength sentinel
        tokenCount tokenTable offsetTable) := by
  rw [tableauOuterQ2_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [tableauDepthTwoTerms, tableauDepthThreeTerms, Rew.q]
  · exact Empty.elim coordinate

private theorem tableauDepthTwoQ_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.embSubsts (tableauDepthTwoTerms payload payloadLength sentinel
      tokenCount tokenTable offsetTable)).q =
      Rew.embSubsts (tableauDepthThreeTerms payload payloadLength sentinel
        tokenCount tokenTable offsetTable) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [tableauDepthTwoTerms, tableauDepthThreeTerms, Rew.q]
  · exact Empty.elim coordinate

private theorem tableauOuterQ4_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.embSubsts (tableauOuterTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)).q.q.q.q =
      Rew.embSubsts (tableauDepthFourTerms payload payloadLength sentinel
        tokenCount tokenTable offsetTable) := by
  rw [tableauOuterQ3_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [tableauDepthThreeTerms, tableauDepthFourTerms, shift4, Rew.q]
  · exact Empty.elim coordinate

private theorem tableauDepthThreeQ_eq_embSubsts
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (Rew.embSubsts (tableauDepthThreeTerms payload payloadLength sentinel
      tokenCount tokenTable offsetTable)).q =
      Rew.embSubsts (tableauDepthFourTerms payload payloadLength sentinel
        tokenCount tokenTable offsetTable) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [tableauDepthThreeTerms, tableauDepthFourTerms, shift4, Rew.q]
  · exact Empty.elim coordinate

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : LO.FirstOrder.Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold LO.FirstOrder.Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem rewriting_termOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : LO.FirstOrder.Semiterm.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting (operator.operator terms) =
      operator.operator (rewriting ∘ terms) := by
  unfold LO.FirstOrder.Semiterm.Operator.operator
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting (Rew.subst terms (Rew.emb operator.term)) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity)) operator.term := by
      rw [Rew.comp_app, Rew.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity)) operator.term := by
      rw [hcomposition]
    _ = Rew.subst (rewriting ∘ terms) (Rew.emb operator.term) := by
      rw [Rew.comp_app]

private theorem rewriting_arithmeticOne
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity) :
    rewriting (‘1’ : LO.FirstOrder.ArithmeticSemiterm
        sourceVariables sourceArity) =
      (‘1’ : LO.FirstOrder.ArithmeticSemiterm
        targetVariables targetArity) := by
  rw [rewriting_termOperator]
  congr 1
  funext coordinate
  exact Fin.elim0 coordinate

private theorem rewriting_arithmeticZero
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity) :
    rewriting (‘0’ : LO.FirstOrder.ArithmeticSemiterm
        sourceVariables sourceArity) =
      (‘0’ : LO.FirstOrder.ArithmeticSemiterm
        targetVariables targetArity) := by
  rw [rewriting_termOperator]
  congr 1
  funext coordinate
  exact Fin.elim0 coordinate

private theorem rewriting_arithmeticAdd
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (left right : LO.FirstOrder.ArithmeticSemiterm
      sourceVariables sourceArity) :
    rewriting (‘!!left + !!right’) =
      (‘!!(rewriting left) + !!(rewriting right)’ :
        LO.FirstOrder.ArithmeticSemiterm targetVariables targetArity) := by
  rw [rewriting_termOperator]
  congr 1
  funext coordinate
  fin_cases coordinate <;> rfl

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : LO.FirstOrder.ArithmeticSemiformula sourceVariables
      (sourceArity + 1))
    (bound : LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm sourceVariables
              (sourceArity + 1)), Rew.bShift bound] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm targetVariables
              (targetArity + 1)), Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold LO.FirstOrder.Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

private def tableauRowCore
    (payload payloadLength tokenTable offsetTable : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift4 (shortBinaryNumeralTerm tokenTable),
        shift4 (shortBinaryNumeralTerm payloadLength),
        (#3 : LO.FirstOrder.ArithmeticSemiterm Nat 4), #2]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![shift4 (shortBinaryNumeralTerm offsetTable),
          shift4 (shortBinaryNumeralTerm payloadLength),
          (#3 : LO.FirstOrder.ArithmeticSemiterm Nat 4), #1]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![shift4 (shortBinaryNumeralTerm offsetTable),
            shift4 (shortBinaryNumeralTerm payloadLength),
            (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Nat 4), #0]) ⋏
        ((Rewriting.emb (ξ := Nat) compactBinaryNatTokenSegmentDef.val) ⇜
          ![shift4 (shortBinaryNumeralTerm payload), #1, #2, #0])))

private def nextWitnessBody
    (payload payloadLength sentinel tokenTable offsetTable : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 4 :=
  “#0 < !!(shift4 (shortBinaryNumeralTerm sentinel)) + 1” ⋏
    tableauRowCore payload payloadLength tokenTable offsetTable

private def offsetWitnessBody
    (payload payloadLength sentinel tokenTable offsetTable : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 3 :=
  “#0 <
      !!(Rew.bShift (Rew.bShift (Rew.bShift
        (shortBinaryNumeralTerm sentinel)))) + 1” ⋏
    (∃⁰ nextWitnessBody
      payload payloadLength sentinel tokenTable offsetTable)

private def tokenWitnessBody
    (payload payloadLength sentinel tokenTable offsetTable : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  “#0 <
      !!(Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sentinel))) + 1” ⋏
    (∃⁰ offsetWitnessBody
      payload payloadLength sentinel tokenTable offsetTable)

private def tableauRowBody
    (payload payloadLength sentinel tokenTable offsetTable : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∃⁰ tokenWitnessBody
    payload payloadLength sentinel tokenTable offsetTable

private def tableauExponentialFormula
    (payloadLength sentinel : Nat) : ArithmeticProposition :=
  exponentialAtValuationFormula
    (shortBinaryNumeralTerm sentinel)
    (shortBinaryNumeralTerm payloadLength)

private def tableauTokenCountBoundFormula
    (payloadLength tokenCount : Nat) : ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm tokenCount) ≤
    !!(shortBinaryNumeralTerm payloadLength) + 1”

private def tableauUniversalFormula
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    ArithmeticProposition :=
  (tableauRowBody payload payloadLength sentinel tokenTable offsetTable).ballLT
    (shortBinaryNumeralTerm tokenCount)

def compactBinaryNatTokenStreamTableauDecomposedFormula
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    ArithmeticProposition :=
  tableauExponentialFormula payloadLength sentinel ⋏
    (tableauTokenCountBoundFormula payloadLength tokenCount ⋏
      (compactFixedWidthEntryClosedFormula
          offsetTable payloadLength 0 0 ⋏
        (compactFixedWidthEntryClosedFormula
            offsetTable payloadLength tokenCount payloadLength ⋏
          tableauUniversalFormula payload payloadLength sentinel tokenCount
            tokenTable offsetTable)))

private theorem bShift_tableauSourceNextBound :
    Rew.bShift
        (‘#5 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 9) =
      (‘#6 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 10) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem bShift_tableauSourceOffsetBound :
    Rew.bShift
        (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 8) =
      (‘#5 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 9) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem bShift_tableauSourceTokenBound :
    Rew.bShift
        (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 8) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem tableauSourceUniversalFormula_eq_normalized :
    tableauSourceUniversalFormula =
      tableauSourceRowBody.ballLT
        (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 6) := by
  unfold tableauSourceUniversalFormula tableauSourceRowBody
  unfold tableauSourceTokenBody tableauSourceOffsetBody
  unfold tableauSourceNextBody
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
  unfold LO.FirstOrder.Semiformula.bexsLT
  unfold LO.FirstOrder.bexs
  rw [bShift_tableauSourceNextBound,
    bShift_tableauSourceOffsetBound,
    bShift_tableauSourceTokenBound]

private theorem tableauSourceRowCore_rewrite
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Rew.embSubsts
        (tableauDepthFourTerms payload payloadLength sentinel tokenCount
          tokenTable offsetTable) ▹ tableauSourceRowCore =
      tableauRowCore payload payloadLength tokenTable offsetTable := by
  let rewriting := Rew.embSubsts
    (tableauDepthFourTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)
  have htoken : rewriting ∘
        ![(#8 : LO.FirstOrder.ArithmeticSemiterm Empty 10), #5, #3, #2] =
      ![shift4 (shortBinaryNumeralTerm tokenTable),
        shift4 (shortBinaryNumeralTerm payloadLength), #3, #2] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [rewriting, tableauDepthFourTerms, shift4, Function.comp_def]
  have hoffset : rewriting ∘
        ![(#9 : LO.FirstOrder.ArithmeticSemiterm Empty 10), #5, #3, #1] =
      ![shift4 (shortBinaryNumeralTerm offsetTable),
        shift4 (shortBinaryNumeralTerm payloadLength), #3, #1] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [rewriting, tableauDepthFourTerms, shift4, Function.comp_def]
  have hnext : rewriting ∘
        ![(#9 : LO.FirstOrder.ArithmeticSemiterm Empty 10), #5,
          (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 10), #0] =
      ![shift4 (shortBinaryNumeralTerm offsetTable),
        shift4 (shortBinaryNumeralTerm payloadLength),
        (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Nat 4), #0] := by
    funext coordinate
    fin_cases coordinate
    · simp [rewriting, tableauDepthFourTerms, shift4, Function.comp_def]
    · simp [rewriting, tableauDepthFourTerms, shift4, Function.comp_def]
    · change rewriting
          (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 10) =
        (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Nat 4)
      rw [rewriting_arithmeticAdd, rewriting_arithmeticOne]
      simp [rewriting, tableauDepthFourTerms]
    · simp [rewriting, tableauDepthFourTerms, shift4, Function.comp_def]
  have hsegment : rewriting ∘
        ![(#4 : LO.FirstOrder.ArithmeticSemiterm Empty 10), #1, #2, #0] =
      ![shift4 (shortBinaryNumeralTerm payload), #1, #2, #0] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [rewriting, tableauDepthFourTerms, shift4, Function.comp_def]
  change rewriting ▹ tableauSourceRowCore = _
  unfold tableauSourceRowCore tableauRowCore
  simp only [LogicalConnective.HomClass.map_and,
    rewriting_emptyFormulaSubstitution]
  rw [htoken, hoffset, hnext, hsegment]

private theorem tableauSourceNextBody_rewrite
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Rew.embSubsts
        (tableauDepthFourTerms payload payloadLength sentinel tokenCount
          tokenTable offsetTable) ▹ tableauSourceNextBody =
      nextWitnessBody payload payloadLength sentinel tokenTable offsetTable := by
  let rewriting := Rew.embSubsts
    (tableauDepthFourTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)
  have hterms : rewriting ∘
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 10),
          (‘#6 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 10)] =
      ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 4),
        (‘!!(shift4 (shortBinaryNumeralTerm sentinel)) + 1’ :
          LO.FirstOrder.ArithmeticSemiterm Nat 4)] := by
    funext coordinate
    fin_cases coordinate
    · simp [rewriting, tableauDepthFourTerms]
    · change rewriting
          (‘#6 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 10) =
        (‘!!(shift4 (shortBinaryNumeralTerm sentinel)) + 1’ :
          LO.FirstOrder.ArithmeticSemiterm Nat 4)
      rw [rewriting_arithmeticAdd, rewriting_arithmeticOne]
      simp [rewriting, tableauDepthFourTerms, shift4]
  have hguard : rewriting ▹
        (“#0 < #6 + 1” : LO.FirstOrder.ArithmeticSemiformula Empty 10) =
      (“#0 < !!(shift4 (shortBinaryNumeralTerm sentinel)) + 1” :
        LO.FirstOrder.ArithmeticSemiformula Nat 4) := by
    change rewriting ▹
        LO.FirstOrder.Semiformula.Operator.LT.lt.operator
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 10),
            (‘#6 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 10)] =
      LO.FirstOrder.Semiformula.Operator.LT.lt.operator
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 4),
          (‘!!(shift4 (shortBinaryNumeralTerm sentinel)) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 4)]
    rw [rewriting_formulaOperator, hterms]
  change rewriting ▹ tableauSourceNextBody = _
  unfold tableauSourceNextBody nextWitnessBody
  simp only [LogicalConnective.HomClass.map_and]
  rw [hguard, tableauSourceRowCore_rewrite]

private theorem tableauSourceOffsetBody_rewrite
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Rew.embSubsts
        (tableauDepthThreeTerms payload payloadLength sentinel tokenCount
          tokenTable offsetTable) ▹ tableauSourceOffsetBody =
      offsetWitnessBody payload payloadLength sentinel tokenTable offsetTable := by
  let rewriting := Rew.embSubsts
    (tableauDepthThreeTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)
  have hterms : rewriting ∘
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 9),
          (‘#5 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 9)] =
      ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3),
        (‘!!(Rew.bShift (Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm sentinel)))) + 1’ :
          LO.FirstOrder.ArithmeticSemiterm Nat 3)] := by
    funext coordinate
    fin_cases coordinate
    · simp [rewriting, tableauDepthThreeTerms]
    · change rewriting
          (‘#5 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 9) =
        (‘!!(Rew.bShift (Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm sentinel)))) + 1’ :
          LO.FirstOrder.ArithmeticSemiterm Nat 3)
      rw [rewriting_arithmeticAdd, rewriting_arithmeticOne]
      simp [rewriting, tableauDepthThreeTerms]
  have hguard : rewriting ▹
        (“#0 < #5 + 1” : LO.FirstOrder.ArithmeticSemiformula Empty 9) =
      (“#0 <
        !!(Rew.bShift (Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm sentinel)))) + 1” :
        LO.FirstOrder.ArithmeticSemiformula Nat 3) := by
    change rewriting ▹
        LO.FirstOrder.Semiformula.Operator.LT.lt.operator
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 9),
            (‘#5 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 9)] =
      LO.FirstOrder.Semiformula.Operator.LT.lt.operator
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3),
          (‘!!(Rew.bShift (Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm sentinel)))) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 3)]
    rw [rewriting_formulaOperator, hterms]
  change rewriting ▹ tableauSourceOffsetBody = _
  unfold tableauSourceOffsetBody offsetWitnessBody
  simp only [LogicalConnective.HomClass.map_and, Rewriting.app_exs]
  rw [hguard, tableauDepthThreeQ_eq_embSubsts,
    tableauSourceNextBody_rewrite]

private theorem tableauSourceTokenBody_rewrite
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Rew.embSubsts
        (tableauDepthTwoTerms payload payloadLength sentinel tokenCount
          tokenTable offsetTable) ▹ tableauSourceTokenBody =
      tokenWitnessBody payload payloadLength sentinel tokenTable offsetTable := by
  let rewriting := Rew.embSubsts
    (tableauDepthTwoTerms payload payloadLength sentinel tokenCount
      tokenTable offsetTable)
  have hterms : rewriting ∘
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 8),
          (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 8)] =
      ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2),
        (‘!!(Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm sentinel))) + 1’ :
          LO.FirstOrder.ArithmeticSemiterm Nat 2)] := by
    funext coordinate
    fin_cases coordinate
    · simp [rewriting, tableauDepthTwoTerms]
    · change rewriting
          (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 8) =
        (‘!!(Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm sentinel))) + 1’ :
          LO.FirstOrder.ArithmeticSemiterm Nat 2)
      rw [rewriting_arithmeticAdd, rewriting_arithmeticOne]
      simp [rewriting, tableauDepthTwoTerms]
  have hguard : rewriting ▹
        (“#0 < #4 + 1” : LO.FirstOrder.ArithmeticSemiformula Empty 8) =
      (“#0 <
        !!(Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm sentinel))) + 1” :
        LO.FirstOrder.ArithmeticSemiformula Nat 2) := by
    change rewriting ▹
        LO.FirstOrder.Semiformula.Operator.LT.lt.operator
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 8),
            (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 8)] =
      LO.FirstOrder.Semiformula.Operator.LT.lt.operator
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2),
          (‘!!(Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm sentinel))) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 2)]
    rw [rewriting_formulaOperator, hterms]
  change rewriting ▹ tableauSourceTokenBody = _
  unfold tableauSourceTokenBody tokenWitnessBody
  simp only [LogicalConnective.HomClass.map_and, Rewriting.app_exs]
  rw [hguard, tableauDepthTwoQ_eq_embSubsts,
    tableauSourceOffsetBody_rewrite]

private theorem tableauSourceRowBody_rewrite
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Rew.embSubsts
        (tableauDepthOneTerms payload payloadLength sentinel tokenCount
          tokenTable offsetTable) ▹ tableauSourceRowBody =
      tableauRowBody payload payloadLength sentinel tokenTable offsetTable := by
  unfold tableauSourceRowBody tableauRowBody
  simp only [Rewriting.app_exs]
  rw [tableauDepthOneQ_eq_embSubsts, tableauSourceTokenBody_rewrite]

private theorem tableauSourceUniversalFormula_rewrite
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Rew.embSubsts
        (tableauOuterTerms payload payloadLength sentinel tokenCount tokenTable
          offsetTable) ▹ tableauSourceUniversalFormula =
      tableauUniversalFormula payload payloadLength sentinel tokenCount
        tokenTable offsetTable := by
  rw [tableauSourceUniversalFormula_eq_normalized, rewriting_ballLT]
  rw [tableauOuterQ1_eq_embSubsts, tableauSourceRowBody_rewrite]
  unfold tableauUniversalFormula
  congr 1

/-- Full syntactic decomposition of the quoted six-coordinate definition.
In particular this identifies the three explicit row existentials and their
successor guards, not merely the top-level semantic proposition. -/
theorem compactBinaryNatTokenStreamTableauClosedFormula_formula_alignment
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    compactBinaryNatTokenStreamTableauClosedFormula payload payloadLength
        sentinel tokenCount tokenTable offsetTable =
      compactBinaryNatTokenStreamTableauDecomposedFormula payload payloadLength
        sentinel tokenCount tokenTable offsetTable := by
  unfold compactBinaryNatTokenStreamTableauClosedFormula
  change Rew.subst
      (tableauOuterTerms payload payloadLength sentinel tokenCount tokenTable
        offsetTable) ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 6 Nat 6) ▹
        compactBinaryNatTokenStreamTableauDef.val) = _
  rw [← TransitiveRewriting.comp_app,
    tableauOuterRewriting_eq_embSubsts]
  rw [compactBinaryNatTokenStreamTableauDef_val_eq_sourceDecomposed]
  let rewriting := Rew.embSubsts
    (tableauOuterTerms payload payloadLength sentinel tokenCount tokenTable
      offsetTable)
  change rewriting ▹ tableauSourceDecomposedFormula =
    compactBinaryNatTokenStreamTableauDecomposedFormula payload payloadLength
      sentinel tokenCount tokenTable offsetTable
  have hexponentialTerms : rewriting ∘
        ![(#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #1] =
      ![shortBinaryNumeralTerm sentinel,
        shortBinaryNumeralTerm payloadLength] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [rewriting, tableauOuterTerms, Function.comp_def]
  have hexponential : rewriting ▹
        (expDef.val ⇜
          ![(#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #1]) =
      tableauExponentialFormula payloadLength sentinel := by
    rw [rewriting_emptyFormulaSubstitution, hexponentialTerms]
    rfl
  have hcount : rewriting ▹
        (“#3 ≤ #1 + 1” : LO.FirstOrder.ArithmeticSemiformula Empty 6) =
      tableauTokenCountBoundFormula payloadLength tokenCount := by
    have hterms : rewriting ∘
          ![(#3 : LO.FirstOrder.ArithmeticSemiterm Empty 6),
            (‘#1 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 6)] =
        ![shortBinaryNumeralTerm tokenCount,
          (‘!!(shortBinaryNumeralTerm payloadLength) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0)] := by
      funext coordinate
      fin_cases coordinate
      · simp [rewriting, tableauOuterTerms]
      · change rewriting
            (‘#1 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
          (‘!!(shortBinaryNumeralTerm payloadLength) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0)
        rw [rewriting_arithmeticAdd, rewriting_arithmeticOne]
        simp [rewriting, tableauOuterTerms]
    unfold tableauTokenCountBoundFormula
    change rewriting ▹
        LO.FirstOrder.Semiformula.Operator.LE.le.operator
          ![(#3 : LO.FirstOrder.ArithmeticSemiterm Empty 6),
            (‘#1 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 6)] =
      LO.FirstOrder.Semiformula.Operator.LE.le.operator
        ![shortBinaryNumeralTerm tokenCount,
          (‘!!(shortBinaryNumeralTerm payloadLength) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0)]
    rw [rewriting_formulaOperator, hterms]
  have hzeroTerms : rewriting ∘
        ![(#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #1,
          tableauSourceZeroTerm, tableauSourceZeroTerm] =
      ![shortBinaryNumeralTerm offsetTable,
        shortBinaryNumeralTerm payloadLength,
        shortBinaryNumeralTerm 0, shortBinaryNumeralTerm 0] := by
    funext coordinate
    fin_cases coordinate
    · simp [rewriting, tableauOuterTerms, Function.comp_def]
    · simp [rewriting, tableauOuterTerms, Function.comp_def]
    · change rewriting tableauSourceZeroTerm = shortBinaryNumeralTerm 0
      rw [show tableauSourceZeroTerm =
          (‘0’ : LO.FirstOrder.ArithmeticSemiterm Empty 6) by rfl,
        rewriting_arithmeticZero]
      simp [shortBinaryNumeralTerm,
        FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
        FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
        LO.FirstOrder.Semiterm.Operator.operator,
        LO.FirstOrder.Semiterm.Operator.numeral_zero,
        LO.FirstOrder.Semiterm.Operator.Zero.term_eq]
    · change rewriting tableauSourceZeroTerm = shortBinaryNumeralTerm 0
      rw [show tableauSourceZeroTerm =
          (‘0’ : LO.FirstOrder.ArithmeticSemiterm Empty 6) by rfl,
        rewriting_arithmeticZero]
      simp [shortBinaryNumeralTerm,
        FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
        FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
        LO.FirstOrder.Semiterm.Operator.operator,
        LO.FirstOrder.Semiterm.Operator.numeral_zero,
        LO.FirstOrder.Semiterm.Operator.Zero.term_eq]
  have hzero : rewriting ▹
        (compactFixedWidthEntryDef.val ⇜
          ![(#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #1,
            tableauSourceZeroTerm, tableauSourceZeroTerm]) =
      compactFixedWidthEntryClosedFormula
        offsetTable payloadLength 0 0 := by
    unfold compactFixedWidthEntryClosedFormula
    rw [rewriting_emptyFormulaSubstitution, hzeroTerms]
  have hlastTerms : rewriting ∘
        ![(#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #1, #3, #1] =
      ![shortBinaryNumeralTerm offsetTable,
        shortBinaryNumeralTerm payloadLength,
        shortBinaryNumeralTerm tokenCount,
        shortBinaryNumeralTerm payloadLength] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [rewriting, tableauOuterTerms, Function.comp_def]
  have hlast : rewriting ▹
        (compactFixedWidthEntryDef.val ⇜
          ![(#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #1, #3, #1]) =
      compactFixedWidthEntryClosedFormula offsetTable payloadLength
        tokenCount payloadLength := by
    unfold compactFixedWidthEntryClosedFormula
    rw [rewriting_emptyFormulaSubstitution, hlastTerms]
  have huniversal : rewriting ▹ tableauSourceUniversalFormula =
      tableauUniversalFormula payload payloadLength sentinel tokenCount
        tokenTable offsetTable :=
    tableauSourceUniversalFormula_rewrite payload payloadLength sentinel
      tokenCount tokenTable offsetTable
  unfold tableauSourceDecomposedFormula
  unfold compactBinaryNatTokenStreamTableauDecomposedFormula
  simp only [LogicalConnective.HomClass.map_and]
  rw [hexponential, hcount, hzero, hlast, huniversal]

private theorem termValue_eq_of_agreeOn_freeVariables
    (source target : Nat -> Nat) (term : ValuationTerm)
    (hagrees : forall index, index ∈ term.freeVariables ->
      source index = target index) :
    termValue source term = termValue target term := by
  unfold termValue
  exact LO.FirstOrder.Semiterm.val_eq_of_funEqOn term hagrees

private theorem formulaValue_iff_of_agreeOn_freeVariables
    (source target : Nat -> Nat) (formula : ValuationFormula)
    (hagrees : forall index, index ∈ formula.freeVariables ->
      source index = target index) :
    formulaValue source formula <-> formulaValue target formula := by
  unfold formulaValue
  exact LO.FirstOrder.Semiformula.eval_iff_of_funEqOn formula hagrees

mutual

  /-- Rebuild a hybrid certificate under a valuation that agrees on every
  free variable actually occurring in the certified formula. -/
  private noncomputable def revalueHybridCertificate :
      {source : Nat -> Nat} -> {formula : ValuationFormula} ->
      HybridCertificate source formula ->
      (target : Nat -> Nat) ->
      (forall index, index ∈ formula.freeVariables ->
        source index = target index) ->
      HybridCertificate target formula
    | _, _, .verum _, target, _ => .verum target
    | _, _, .positiveAtomic source relationSymbol args htruth,
        target, hagrees =>
      .positiveAtomic target relationSymbol args
        ((formulaValue_iff_of_agreeOn_freeVariables source target
          (.rel relationSymbol args) hagrees).mp htruth)
    | _, _, .negativeAtomic source relationSymbol args htruth,
        target, hagrees =>
      .negativeAtomic target relationSymbol args
        ((formulaValue_iff_of_agreeOn_freeVariables source target
          (.nrel relationSymbol args) hagrees).mp htruth)
    | _, _, .exponential source valueTerm exponentTerm hvalue,
        target, hagrees => by
      have hvalueTerm : termValue source valueTerm =
          termValue target valueTerm :=
        termValue_eq_of_agreeOn_freeVariables source target valueTerm
          (fun index hindex => hagrees index (by
            rw [exponentialAtValuationFormula_freeVariables]
            exact Finset.mem_union_left _ hindex))
      have hexponentTerm : termValue source exponentTerm =
          termValue target exponentTerm :=
        termValue_eq_of_agreeOn_freeVariables source target exponentTerm
          (fun index hindex => hagrees index (by
            rw [exponentialAtValuationFormula_freeVariables]
            exact Finset.mem_union_right _ hindex))
      exact .exponential target valueTerm exponentTerm (by
        rw [← hvalueTerm, ← hexponentTerm]
        exact hvalue)
    | _, _, .binaryLength source sizeTerm valueTerm hsize,
        target, hagrees => by
      have hsizeTerm : termValue source sizeTerm =
          termValue target sizeTerm :=
        termValue_eq_of_agreeOn_freeVariables source target sizeTerm
          (fun index hindex => hagrees index (by
            rw [binaryLengthAtValuationFormula_freeVariables]
            exact Finset.mem_union_left _ hindex))
      have hvalueTerm : termValue source valueTerm =
          termValue target valueTerm :=
        termValue_eq_of_agreeOn_freeVariables source target valueTerm
          (fun index hindex => hagrees index (by
            rw [binaryLengthAtValuationFormula_freeVariables]
            exact Finset.mem_union_right _ hindex))
      exact .binaryLength target sizeTerm valueTerm (by
        rw [← hsizeTerm, ← hvalueTerm]
        exact hsize)
    | _, _, .binaryBit expected source indexTerm valueTerm hbit hvariables,
        target, hagrees => by
      have hindexTerm : termValue source indexTerm =
          termValue target indexTerm :=
        termValue_eq_of_agreeOn_freeVariables source target indexTerm
          (fun index hindex => hagrees index
            (hvariables (Finset.mem_union_left _ hindex)))
      have hvalueTerm : termValue source valueTerm =
          termValue target valueTerm :=
        termValue_eq_of_agreeOn_freeVariables source target valueTerm
          (fun index hindex => hagrees index
            (hvariables (Finset.mem_union_right _ hindex)))
      exact .binaryBit expected target indexTerm valueTerm (by
        rw [← hindexTerm, ← hvalueTerm]
        exact hbit) hvariables
    | _, _, .conjunction leftCertificate rightCertificate,
        target, hagrees =>
      .conjunction
        (revalueHybridCertificate leftCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
        (revalueHybridCertificate rightCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
    | _, _, .disjunctionLeft leftCertificate, target, hagrees =>
      .disjunctionLeft
        (revalueHybridCertificate leftCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
    | _, _, .disjunctionRight rightCertificate, target, hagrees =>
      .disjunctionRight
        (revalueHybridCertificate rightCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
    | _, _, .existsWitness body witness bodyCertificate,
        target, hagrees =>
      .existsWitness body witness
        (revalueHybridCertificate bodyCertificate target
          (fun index hindex => hagrees index (by
            simpa using
              shortBinarySubstitution_freeVariables_subset
                body witness hindex)))
    | source, _, .boundedUniversal boundSource body branches,
        target, hagrees => by
      have hbody : forall index, index ∈ body.freeVariables ->
          source index = target index := fun index hindex =>
        hagrees index
          (body_freeVariables_subset_universal boundSource body hindex)
      have hboundValue : termValue source boundSource =
          termValue target boundSource :=
        termValue_eq_of_agreeOn_freeVariables source target boundSource
          (fun index hindex => hagrees index
            (boundSource_freeVariables_subset_universal
              boundSource body hindex))
      exact .boundedUniversal boundSource body
        (hboundValue ▸ revalueHybridBranches branches target hbody)
    | _, _, .cast rfl sourceCertificate, target, hagrees =>
      revalueHybridCertificate sourceCertificate target hagrees

  /-- Transport explicit universal branches while retaining the concrete
  branch head at free variable zero. -/
  private noncomputable def revalueHybridBranches :
      {source : Nat -> Nat} ->
      {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} ->
      {bound : Nat} ->
      HybridBranches source body bound ->
      (target : Nat -> Nat) ->
      (forall index, index ∈ body.freeVariables ->
        source index = target index) ->
      HybridBranches target body bound
    | _, _, _, .nil _ _, target, _ => .nil target _
    | _, _, _, .snoc initial last, target, hagrees => by
      let initial' := revalueHybridBranches initial target hagrees
      let last' := revalueHybridCertificate last
        (extendValuation _ target) (fun index hindex => by
          have hsubset := freeFormula_freeVariables_subset _ hindex
          rcases Finset.mem_insert.mp hsubset with hzero | hshifted
          · subst index
            rfl
          · rcases Finset.mem_image.mp hshifted with
              ⟨sourceIndex, hsourceIndex, rfl⟩
            simp [hagrees sourceIndex hsourceIndex])
      exact .snoc initial' last'

end

private noncomputable def revalueClosedHybridCertificate
    {source : Nat -> Nat} {formula : ValuationFormula}
    (certificate : HybridCertificate source formula)
    (hclosed : formula.freeVariables = ∅)
    (target : Nat -> Nat) :
    HybridCertificate target formula :=
  revalueHybridCertificate certificate target (fun index hindex => by
    rw [hclosed] at hindex
    simp at hindex)

private def rowTokenBody
    (payload payloadLength sentinel tokenTable offsetTable : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (Rew.free (L := ℒₒᵣ) (n := 0)).q ▹
    tokenWitnessBody payload payloadLength sentinel tokenTable offsetTable

private def rowOffsetBody
    (payload payloadLength sentinel tokenTable offsetTable token : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ((Rew.subst ![shortBinaryNumeralTerm token]).q.comp
      (Rew.free (L := ℒₒᵣ) (n := 0)).q.q) ▹
    offsetWitnessBody payload payloadLength sentinel tokenTable offsetTable

private def rowNextBody
    (payload payloadLength sentinel tokenTable offsetTable token offset : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (((Rew.subst ![shortBinaryNumeralTerm offset]).q.comp
      (Rew.subst ![shortBinaryNumeralTerm token]).q.q).comp
        (Rew.free (L := ℒₒᵣ) (n := 0)).q.q.q) ▹
    nextWitnessBody payload payloadLength sentinel tokenTable offsetTable

private def rowWitnessGuardFormula
    (value sentinel : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) <
    !!(shortBinaryNumeralTerm sentinel) + 1”

private def tableauRowPostWitnessFormula
    (payload payloadLength sentinel tokenTable offsetTable
      token offset next : Nat) : ValuationFormula :=
  rowWitnessGuardFormula next sentinel ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm payloadLength)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm token) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm offsetTable)
          (shortBinaryNumeralTerm payloadLength)
          (&0 : ValuationTerm)
          (shortBinaryNumeralTerm offset) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm offsetTable)
            (shortBinaryNumeralTerm payloadLength)
            (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm next) ⋏
          compactBinaryNatTokenSegmentClosedFormula
            payload offset token next)))

private theorem rowTokenInstalledRewriting_eq (token : Nat) :
    (Rew.subst ![shortBinaryNumeralTerm token]).comp
        (Rew.free (L := ℒₒᵣ) (n := 0)).q =
      Rew.bind
        ![shortBinaryNumeralTerm token, (&0 : ValuationTerm)]
        (fun index => &(index + 1)) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [Rew.comp_app, subst_bShiftTerm, q_bvar_one, q_bvar_two]
  · rfl

private theorem rowOffsetInstalledRewriting_eq
    (token offset : Nat) :
    (Rew.subst ![shortBinaryNumeralTerm offset]).comp
        ((Rew.subst ![shortBinaryNumeralTerm token]).q.comp
          (Rew.free (L := ℒₒᵣ) (n := 0)).q.q) =
      Rew.bind
        ![shortBinaryNumeralTerm offset, shortBinaryNumeralTerm token,
          (&0 : ValuationTerm)] (fun index => &(index + 1)) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [Rew.comp_app, subst_bShiftTerm, q_bvar_one, q_bvar_two,
        q_bvar_one_fin3, q_bvar_three]
  · rfl

private theorem rowNextInstalledRewriting_eq
    (token offset next : Nat) :
    (Rew.subst ![shortBinaryNumeralTerm next]).comp
        (((Rew.subst ![shortBinaryNumeralTerm offset]).q.comp
          (Rew.subst ![shortBinaryNumeralTerm token]).q.q).comp
            (Rew.free (L := ℒₒᵣ) (n := 0)).q.q.q) =
      Rew.bind
        ![shortBinaryNumeralTerm next, shortBinaryNumeralTerm offset,
          shortBinaryNumeralTerm token, (&0 : ValuationTerm)]
        (fun index => &(index + 1)) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [Rew.comp_app, subst_bShiftTerm, q_bvar_one, q_bvar_two,
        q_bvar_one_fin3, q_bvar_three]
  · rfl

private theorem tableauRowBody_free_alignment
    (payload payloadLength sentinel tokenTable offsetTable : Nat) :
    Rewriting.free
        (tableauRowBody payload payloadLength sentinel tokenTable offsetTable) =
      ∃⁰ rowTokenBody
        payload payloadLength sentinel tokenTable offsetTable := by
  unfold tableauRowBody rowTokenBody
  simp only [Rewriting.app_exs]

private theorem rowTokenBody_subst_alignment
    (payload payloadLength sentinel tokenTable offsetTable token : Nat) :
    (rowTokenBody payload payloadLength sentinel tokenTable offsetTable)/[
        shortBinaryNumeralTerm token] =
      rowWitnessGuardFormula token sentinel ⋏
        (∃⁰ rowOffsetBody payload payloadLength sentinel tokenTable
          offsetTable token) := by
  unfold rowTokenBody
  change Rew.subst ![shortBinaryNumeralTerm token] ▹
      ((Rew.free (L := ℒₒᵣ) (n := 0)).q ▹
        tokenWitnessBody payload payloadLength sentinel tokenTable
          offsetTable) = _
  rw [← TransitiveRewriting.comp_app, rowTokenInstalledRewriting_eq]
  unfold tokenWitnessBody rowWitnessGuardFormula rowOffsetBody
  simp only [LogicalConnective.HomClass.map_and, Rewriting.app_exs]
  congr 1
  · rw [← rowTokenInstalledRewriting_eq token]
    have hsentinel := rewrite_bShift2_shortBinaryNumeralTerm
      ((Rew.subst ![shortBinaryNumeralTerm token]).comp
        (Rew.free (L := ℒₒᵣ) (n := 1))) sentinel
    simp only [Rew.comp_app] at hsentinel
    simp [Rew.comp_app, hsentinel,
      LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_one,
      LO.FirstOrder.Semiterm.Operator.Add.term_eq,
      LO.FirstOrder.Semiterm.Operator.One.term_eq,
      Rew.func, Matrix.fun_eq_vec_two]
  · congr 1
    exact congrArg
      (fun rewriting => rewriting ▹
        offsetWitnessBody payload payloadLength sentinel tokenTable
          offsetTable)
      (by simpa [Rew.q_comp, rew_comp_assoc] using
        (congrArg Rew.q (rowTokenInstalledRewriting_eq token)).symm)

private theorem rowOffsetBody_subst_alignment
    (payload payloadLength sentinel tokenTable offsetTable token offset : Nat) :
    (rowOffsetBody payload payloadLength sentinel tokenTable offsetTable token)/[
        shortBinaryNumeralTerm offset] =
      rowWitnessGuardFormula offset sentinel ⋏
        (∃⁰ rowNextBody payload payloadLength sentinel tokenTable offsetTable
          token offset) := by
  unfold rowOffsetBody
  change Rew.subst ![shortBinaryNumeralTerm offset] ▹
      (((Rew.subst ![shortBinaryNumeralTerm token]).q.comp
        (Rew.free (L := ℒₒᵣ) (n := 0)).q.q) ▹
          offsetWitnessBody payload payloadLength sentinel tokenTable
            offsetTable) = _
  rw [← TransitiveRewriting.comp_app, rowOffsetInstalledRewriting_eq]
  unfold offsetWitnessBody rowWitnessGuardFormula rowNextBody
  simp only [LogicalConnective.HomClass.map_and, Rewriting.app_exs]
  congr 1
  · rw [← rowOffsetInstalledRewriting_eq token offset]
    have hsentinel := rewrite_bShift3_shortBinaryNumeralTerm
      ((Rew.subst ![shortBinaryNumeralTerm offset]).comp
        ((Rew.subst ![shortBinaryNumeralTerm token]).q.comp
          (Rew.free (L := ℒₒᵣ) (n := 2)))) sentinel
    simp only [Rew.comp_app] at hsentinel
    simp [Rew.comp_app, hsentinel,
      LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_one,
      LO.FirstOrder.Semiterm.Operator.Add.term_eq,
      LO.FirstOrder.Semiterm.Operator.One.term_eq,
      Rew.func, Matrix.fun_eq_vec_two]
  · congr 1
    exact congrArg
      (fun rewriting => rewriting ▹
        nextWitnessBody payload payloadLength sentinel tokenTable
          offsetTable)
      (by simpa [Rew.q_comp, rew_comp_assoc] using
        (congrArg Rew.q
          (rowOffsetInstalledRewriting_eq token offset)).symm)

private theorem rowNextBody_subst_alignment
    (payload payloadLength sentinel tokenTable offsetTable
      token offset next : Nat) :
    (rowNextBody payload payloadLength sentinel tokenTable offsetTable
        token offset)/[shortBinaryNumeralTerm next] =
      tableauRowPostWitnessFormula payload payloadLength sentinel tokenTable
        offsetTable token offset next := by
  unfold rowNextBody
  change Rew.subst ![shortBinaryNumeralTerm next] ▹
      ((((Rew.subst ![shortBinaryNumeralTerm offset]).q.comp
          (Rew.subst ![shortBinaryNumeralTerm token]).q.q).comp
        (Rew.free (L := ℒₒᵣ) (n := 0)).q.q.q) ▹
          nextWitnessBody payload payloadLength sentinel tokenTable
            offsetTable) = _
  rw [← TransitiveRewriting.comp_app, rowNextInstalledRewriting_eq]
  let installed : Rew ℒₒᵣ Nat 4 Nat 0 :=
    Rew.bind
      ![shortBinaryNumeralTerm next, shortBinaryNumeralTerm offset,
        shortBinaryNumeralTerm token, (&0 : ValuationTerm)]
      (fun index => &(index + 1))
  change installed ▹
      nextWitnessBody payload payloadLength sentinel tokenTable offsetTable = _
  unfold nextWitnessBody tableauRowPostWitnessFormula
  unfold rowWitnessGuardFormula tableauRowCore shift4
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactBinaryNatTokenSegmentClosedFormula
  have hpayload := rewrite_bShift4_shortBinaryNumeralTerm installed payload
  have hpayloadLength := rewrite_bShift4_shortBinaryNumeralTerm
    installed payloadLength
  have htokenTable := rewrite_bShift4_shortBinaryNumeralTerm
    installed tokenTable
  have hoffsetTable := rewrite_bShift4_shortBinaryNumeralTerm
    installed offsetTable
  simp [installed, hpayload, hpayloadLength, htokenTable, hoffsetTable,
    Rew.q_subst, Rew.comp_app, Rew.func, subst_bShiftTerm,
    rewrite_bShift4_shortBinaryNumeralTerm,
    Rew.bind_bvar, Rew.bind_fvar,
    rewriting_embeddedFormulaSubstitution, Function.comp_def,
    LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Matrix.fun_eq_vec_two, Matrix.fun_eq_vec_four, Matrix.empty_eq]

private noncomputable def shortNumeralLessThanCertificate
    (valuation : Nat -> Nat) (left right : Nat)
    (hless : left < right) :
    HybridCertificate valuation
      (“!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” : ValuationFormula) := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue valuation (shortBinaryNumeralTerm left) <
          termValue valuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using hless)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def shortNumeralLessOrEqualCertificate
    (valuation : Nat -> Nat) (left right : Nat)
    (hle : left <= right) :
    HybridCertificate valuation
      (“!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” : ValuationFormula) := by
  if hequal : left = right then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        valuation Language.Eq.eq
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
          change termValue valuation (shortBinaryNumeralTerm left) =
            termValue valuation (shortBinaryNumeralTerm right)
          simpa [termValue_shortBinaryNumeralTerm] using hequal)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])
        equality
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct
  else
    have hstrict : left < right := Nat.lt_of_le_of_ne hle hequal
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        valuation Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
          change termValue valuation (shortBinaryNumeralTerm left) <
            termValue valuation (shortBinaryNumeralTerm right)
          simpa [termValue_shortBinaryNumeralTerm] using hstrict)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])
        strict
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct

private noncomputable def rowWitnessGuardCertificate
    (valuation : Nat -> Nat) (value sentinel : Nat)
    (hle : value <= sentinel) :
    HybridCertificate valuation (rowWitnessGuardFormula value sentinel) := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm sentinel) + 1’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm value, rightTerm] (by
        change termValue valuation (shortBinaryNumeralTerm value) <
          termValue valuation rightTerm
        rw [termValue_shortBinaryNumeralTerm]
        simpa [rightTerm, termValue_shortBinaryNumeralAddOne valuation] using
          Nat.lt_succ_of_le hle)
  exact .cast (by
    unfold rowWitnessGuardFormula rightTerm
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def tableauExponentialCertificate
    (payloadLength sentinel : Nat)
    (hsentinel : sentinel = 2 ^ payloadLength) :
    HybridCertificate zeroValuation
      (tableauExponentialFormula payloadLength sentinel) := by
  unfold tableauExponentialFormula
  exact .exponential zeroValuation
    (shortBinaryNumeralTerm sentinel)
    (shortBinaryNumeralTerm payloadLength) (by
      simpa [termValue_shortBinaryNumeralTerm] using hsentinel)

private noncomputable def tableauTokenCountBoundCertificate
    (payloadLength tokenCount : Nat)
    (hcount : tokenCount <= payloadLength + 1) :
    HybridCertificate zeroValuation
      (tableauTokenCountBoundFormula payloadLength tokenCount) := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm tokenCount
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm payloadLength) + 1’
  if hequal : tokenCount = payloadLength + 1 then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq ![leftTerm, rightTerm] (by
          change termValue zeroValuation leftTerm =
            termValue zeroValuation rightTerm
          simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm,
            termValue_shortBinaryNumeralAddOne zeroValuation] using hequal)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![leftTerm, rightTerm]) equality
    exact .cast (by
      unfold tableauTokenCountBoundFormula leftTerm rightTerm
      exact (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm) direct
  else
    have hstrict : tokenCount < payloadLength + 1 :=
      Nat.lt_of_le_of_ne hcount hequal
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] (by
          change termValue zeroValuation leftTerm <
            termValue zeroValuation rightTerm
          simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm,
            termValue_shortBinaryNumeralAddOne zeroValuation] using hstrict)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![leftTerm, rightTerm]) strict
    exact .cast (by
      unfold tableauTokenCountBoundFormula leftTerm rightTerm
      exact (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm) direct

private noncomputable def tableauRowBranchCertificate
    (payload payloadLength sentinel tokenCount tokenTable offsetTable
      publicSize index : Nat)
    (input : ExplicitTokenStreamTableauInput payload payloadLength sentinel
      tokenCount tokenTable offsetTable publicSize)
    (hindex : index < tokenCount) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free
        (tableauRowBody payload payloadLength sentinel tokenTable
          offsetTable)) := by
  let valuation := extendValuation index zeroValuation
  let token := input.tokenAt index
  let offset := input.offsetAt index
  let next := input.nextAt index
  let tokenTerm : ValuationTerm := shortBinaryNumeralTerm token
  let offsetTerm : ValuationTerm := shortBinaryNumeralTerm offset
  let nextTerm : ValuationTerm := shortBinaryNumeralTerm next
  let tokenEntry :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm payloadLength)
      (&0 : ValuationTerm) tokenTerm (by
        simpa [valuation, tokenTerm, token,
          termValue_shortBinaryNumeralTerm] using
          input.tokenEntry index hindex)
  let offsetEntry :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm offsetTable)
      (shortBinaryNumeralTerm payloadLength)
      (&0 : ValuationTerm) offsetTerm (by
        simpa [valuation, offsetTerm, offset,
          termValue_shortBinaryNumeralTerm] using
          input.offsetEntry index hindex)
  let nextEntry :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm offsetTable)
      (shortBinaryNumeralTerm payloadLength)
      (‘&0 + 1’ : ValuationTerm) nextTerm (by
        simpa [valuation, nextTerm, next,
          termValue_shortBinaryNumeralTerm] using
          input.nextEntry index hindex)
  let segmentAtZero :=
    compactBinaryNatTokenSegmentExplicitHybridCertificate
      payload offset token next (input.segment index hindex)
  let segment := revalueClosedHybridCertificate segmentAtZero
    (compactBinaryNatTokenSegmentClosedFormula_freeVariables_eq_empty
      payload offset token next) valuation
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (rowWitnessGuardCertificate valuation next sentinel
      (input.next_le index hindex))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction tokenEntry
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction offsetEntry
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction nextEntry
          segment)))
  let nextExists :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      (rowNextBody payload payloadLength sentinel tokenTable offsetTable
        token offset) next
      (.cast (rowNextBody_subst_alignment payload payloadLength sentinel
        tokenTable offsetTable token offset next).symm post)
  let offsetPost := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (rowWitnessGuardCertificate valuation offset sentinel
      (input.offset_le index hindex)) nextExists
  let offsetExists :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      (rowOffsetBody payload payloadLength sentinel tokenTable offsetTable
        token) offset
      (.cast (rowOffsetBody_subst_alignment payload payloadLength sentinel
        tokenTable offsetTable token offset).symm offsetPost)
  let tokenPost := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (rowWitnessGuardCertificate valuation token sentinel
      (input.token_le index hindex)) offsetExists
  let tokenExists :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      (rowTokenBody payload payloadLength sentinel tokenTable offsetTable)
      token
      (.cast (rowTokenBody_subst_alignment payload payloadLength sentinel
        tokenTable offsetTable token).symm tokenPost)
  exact .cast
    (tableauRowBody_free_alignment payload payloadLength sentinel tokenTable
      offsetTable).symm tokenExists

private noncomputable def tableauUniversalCertificate
    (payload payloadLength sentinel tokenCount tokenTable offsetTable
      publicSize : Nat)
    (input : ExplicitTokenStreamTableauInput payload payloadLength sentinel
      tokenCount tokenTable offsetTable publicSize) :
    HybridCertificate zeroValuation
      (tableauUniversalFormula payload payloadLength sentinel tokenCount
        tokenTable offsetTable) := by
  let body := tableauRowBody payload payloadLength sentinel tokenTable
    offsetTable
  let branches := buildExplicitHybridUniversalBranches tokenCount
    (fun index hindex => tableauRowBranchCertificate payload payloadLength
      sentinel tokenCount tokenTable offsetTable publicSize index input hindex)
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm tokenCount) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm tokenCount)) body) =
      tableauUniversalFormula payload payloadLength sentinel tokenCount
        tokenTable offsetTable
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Fully explicit hybrid certificate for all six closed tableau coordinates.
The public-size parameter is carried by the explicit input for downstream
resource compression; witness selection itself uses only its data fields. -/
noncomputable def compactBinaryNatTokenStreamTableauExplicitHybridCertificate
    (payload payloadLength sentinel tokenCount tokenTable offsetTable
      publicSize : Nat)
    (input : ExplicitTokenStreamTableauInput payload payloadLength sentinel
      tokenCount tokenTable offsetTable publicSize) :
    HybridCertificate zeroValuation
      (compactBinaryNatTokenStreamTableauClosedFormula payload payloadLength
        sentinel tokenCount tokenTable offsetTable) := by
  let decomposed := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (tableauExponentialCertificate payloadLength sentinel input.sentinel_eq)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (tableauTokenCountBoundCertificate payloadLength tokenCount
        input.tokenCount_le)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryExplicitHybridCertificate offsetTable
          payloadLength 0 0 input.offsetZero)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryExplicitHybridCertificate offsetTable
            payloadLength tokenCount payloadLength input.offsetLast)
          (tableauUniversalCertificate payload payloadLength sentinel
            tokenCount tokenTable offsetTable publicSize input))))
  exact .cast
    (compactBinaryNatTokenStreamTableauClosedFormula_formula_alignment
      payload payloadLength sentinel tokenCount tokenTable offsetTable).symm
    decomposed

theorem compactBinaryNatTokenStreamTableauClosedFormula_freeVariables_eq_empty
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    (compactBinaryNatTokenStreamTableauClosedFormula payload payloadLength
      sentinel tokenCount tokenTable offsetTable).freeVariables = ∅ := by
  unfold compactBinaryNatTokenStreamTableauClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

/-- Empty-context checked PA derivation compiled from the explicit hybrid
certificate. -/
noncomputable def compileCompactBinaryNatTokenStreamTableauExplicitHybridContext
    (payload payloadLength sentinel tokenCount tokenTable offsetTable
      publicSize : Nat)
    (input : ExplicitTokenStreamTableauInput payload payloadLength sentinel
      tokenCount tokenTable offsetTable publicSize) :
    CertifiedPAContextProof ∅
      (compactBinaryNatTokenStreamTableauClosedFormula payload payloadLength
        sentinel tokenCount tokenTable offsetTable) := by
  let raw :=
    (compactBinaryNatTokenStreamTableauExplicitHybridCertificate payload
      payloadLength sentinel tokenCount tokenTable offsetTable publicSize
      input).compile
  have hcontext :
      valuationContext
          (compactBinaryNatTokenStreamTableauClosedFormula payload
            payloadLength sentinel tokenCount tokenTable
            offsetTable).freeVariables zeroValuation = ∅ := by
    rw [compactBinaryNatTokenStreamTableauClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Proof-free recursive payload resource for the complete explicit tableau
certificate. -/
noncomputable def compactBinaryNatTokenStreamTableauExplicitHybridStructuralResource
    (payload payloadLength sentinel tokenCount tokenTable offsetTable
      publicSize : Nat)
    (input : ExplicitTokenStreamTableauInput payload payloadLength sentinel
      tokenCount tokenTable offsetTable publicSize) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactBinaryNatTokenStreamTableauExplicitHybridCertificate payload
      payloadLength sentinel tokenCount tokenTable offsetTable publicSize input)

theorem compileCompactBinaryNatTokenStreamTableauExplicitHybridContext_payloadLength_le
    (payload payloadLength sentinel tokenCount tokenTable offsetTable
      publicSize : Nat)
    (input : ExplicitTokenStreamTableauInput payload payloadLength sentinel
      tokenCount tokenTable offsetTable publicSize) :
    (compileCompactBinaryNatTokenStreamTableauExplicitHybridContext payload
      payloadLength sentinel tokenCount tokenTable offsetTable publicSize
      input).payloadLength <=
      compactBinaryNatTokenStreamTableauExplicitHybridStructuralResource
        payload payloadLength sentinel tokenCount tokenTable offsetTable
        publicSize input := by
  unfold compileCompactBinaryNatTokenStreamTableauExplicitHybridContext
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactBinaryNatTokenStreamTableauExplicitHybridCertificate payload
        payloadLength sentinel tokenCount tokenTable offsetTable publicSize
        input)

/-- Canonical specialization using the list-derived explicit row functions
and proofs, without extracting witnesses from tableau semantics. -/
noncomputable def compactBinaryNatTokenStreamTableauCanonicalExplicitHybridCertificate
    (tokens : List Nat) (formulaCode : Nat)
    (hcode : formulaCode =
      FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode tokens) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let offsets := compactBinaryNatTokenOffsets tokens
    HybridCertificate zeroValuation
      (compactBinaryNatTokenStreamTableauClosedFormula
        (compactBinaryNatPayloadValue tokens) width (2 ^ width) tokens.length
        (compactFixedWidthTableCode width tokens)
        (compactFixedWidthTableCode width offsets)) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let offsets := compactBinaryNatTokenOffsets tokens
  exact compactBinaryNatTokenStreamTableauExplicitHybridCertificate
    (compactBinaryNatPayloadValue tokens) width (2 ^ width) tokens.length
    (compactFixedWidthTableCode width tokens)
    (compactFixedWidthTableCode width offsets) (Nat.size formulaCode)
    (canonicalTokenStreamExplicitInput tokens formulaCode hcode)

#print axioms compactBinaryNatTokenStreamTableauClosedFormula_formula_alignment
#print axioms compactBinaryNatTokenStreamTableauExplicitHybridCertificate
#print axioms compileCompactBinaryNatTokenStreamTableauExplicitHybridContext
#print axioms compileCompactBinaryNatTokenStreamTableauExplicitHybridContext_payloadLength_le

end FoundationCompactPAExplicitTokenStreamTableauHybridCertificate
