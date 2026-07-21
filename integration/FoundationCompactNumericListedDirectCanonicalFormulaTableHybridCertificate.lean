import integration.FoundationCompactNumericListedDirectCanonicalFormulaTableInternalBounds
import integration.FoundationCompactNumericListedDirectPredicateMatrixHybridCompiler
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPAExplicitTokenStreamTableauHybridCertificate

/-!
# Explicit outer witnesses for the canonical formula-token tableau

This module retains the legacy outer-witness route and adds a fully explicit
route.  The latter fixes the payload, sentinel, and every token-row witness
before compilation; it does not invoke the Sigma-zero truth fallback.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedAcceptedDirectPACompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectCanonicalFormulaTableInternalBounds
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaBuilder
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitTokenStreamTableauHybridCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation

private theorem compactCanonicalFormulaTable_arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem compactCanonicalFormulaTable_termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [compactCanonicalFormulaTable_arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem compactCanonicalFormulaTable_termValue_arithmeticOne
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactCanonicalFormulaTableClosedFormula
    (tokens : List Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  (Rewriting.emb (ξ := Nat)
      compactCanonicalPackedTokenStreamTableauAtWidthDef.val) ⇜
    ![shortBinaryNumeralTerm (compactAdditivePackedCode tokens),
      shortBinaryNumeralTerm tokens.length,
      shortBinaryNumeralTerm (compactFixedWidthTableCode width tokens),
      shortBinaryNumeralTerm (compactFixedWidthTableCode width
        (compactBinaryNatTokenOffsets tokens)),
      shortBinaryNumeralTerm width]

/-- The same closed canonical-table formula with an externally named code.
The equality argument of the explicit certificate below must identify this code
with the canonical additive packed code; no witness is recovered from it. -/
def compactCanonicalFormulaTableClosedFormulaAtCode
    (tokens : List Nat) (code : Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  (Rewriting.emb (ξ := Nat)
      compactCanonicalPackedTokenStreamTableauAtWidthDef.val) ⇜
    ![shortBinaryNumeralTerm code,
      shortBinaryNumeralTerm tokens.length,
      shortBinaryNumeralTerm (compactFixedWidthTableCode width tokens),
      shortBinaryNumeralTerm (compactFixedWidthTableCode width
        (compactBinaryNatTokenOffsets tokens)),
      shortBinaryNumeralTerm width]

theorem compactCanonicalFormulaTableClosedFormulaAtCode_eq
    (tokens : List Nat) (code : Nat)
    (hcode : code = compactAdditivePackedCode tokens) :
    compactCanonicalFormulaTableClosedFormulaAtCode tokens code =
      compactCanonicalFormulaTableClosedFormula tokens := by
  subst code
  rfl

/-- Formula identity fixing all five public coordinates to canonical values. -/
theorem compactCanonicalFormulaTableClosedFormula_identity
    (tokens : List Nat) :
    compactCanonicalFormulaTableClosedFormula tokens =
      let width := (compactBinaryNatPayloadBits tokens).length
      (Rewriting.emb (ξ := Nat)
          compactCanonicalPackedTokenStreamTableauAtWidthDef.val) ⇜
        ![shortBinaryNumeralTerm (compactAdditivePackedCode tokens),
          shortBinaryNumeralTerm tokens.length,
          shortBinaryNumeralTerm (compactFixedWidthTableCode width tokens),
          shortBinaryNumeralTerm (compactFixedWidthTableCode width
            (compactBinaryNatTokenOffsets tokens)),
          shortBinaryNumeralTerm width] := by
  rfl

theorem compactCanonicalFormulaTableClosedFormula_sigmaZero
    (tokens : List Nat) :
    Hierarchy Polarity.sigma 0
      (compactCanonicalFormulaTableClosedFormula tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  exact
    (compactCanonicalPackedTokenStreamTableauAtWidthDef_sigmaZero.rew
      Rew.emb).rew
        (Rew.subst
          ![shortBinaryNumeralTerm (compactAdditivePackedCode tokens),
            shortBinaryNumeralTerm tokens.length,
            shortBinaryNumeralTerm
              (compactFixedWidthTableCode width tokens),
            shortBinaryNumeralTerm
              (compactFixedWidthTableCode width
                (compactBinaryNatTokenOffsets tokens)),
            shortBinaryNumeralTerm width])

theorem compactCanonicalFormulaTableClosedFormula_freeVariables_eq_empty
    (tokens : List Nat) :
    (compactCanonicalFormulaTableClosedFormula tokens).freeVariables = ∅ := by
  let width := (compactBinaryNatPayloadBits tokens).length
  apply embeddedClosedSubstitution_freeVariables_eq_empty
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem compactCanonicalFormulaTableClosedFormula_truth
    (tokens : List Nat) :
    formulaValue zeroValuation
      (compactCanonicalFormulaTableClosedFormula tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let offsetTable := compactFixedWidthTableCode width
    (compactBinaryNatTokenOffsets tokens)
  unfold compactCanonicalFormulaTableClosedFormula formulaValue
  rw [LO.FirstOrder.Semiformula.eval_substs]
  have hvalues :
      (LO.FirstOrder.Semiterm.val ![] zeroValuation ∘
        ![shortBinaryNumeralTerm (compactAdditivePackedCode tokens),
          shortBinaryNumeralTerm tokens.length,
          shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm offsetTable,
          shortBinaryNumeralTerm width]) =
        ![compactAdditivePackedCode tokens, tokens.length,
          tokenTable, offsetTable, width] := by
    funext coordinate
    fin_cases coordinate <;>
      exact termValue_shortBinaryNumeralTerm zeroValuation _
  rw [hvalues, LO.FirstOrder.Semiformula.eval_emb]
  exact (compactCanonicalPackedTokenStreamTableauAtWidthDef_spec
    (compactAdditivePackedCode tokens) tokens.length tokenTable offsetTable
      width).2 (by
        simpa only [width, tokenTable, offsetTable] using
          compactCanonicalPackedTokenStreamTableauAtWidth_canonical tokens)

private def compactCanonicalFormulaTableSourcePayloadTail :
    LO.FirstOrder.ArithmeticSemiformula Empty 6 :=
  “#5 ≤ #1 ∧
    ∃ sentinel <⁺ #1,
      !expDef sentinel #6 ∧
      #1 < sentinel ∧
      #2 = #1 + sentinel ∧
      !(compactBinaryNatTokenStreamTableauDef)
        #1 #6 sentinel #3 #4 #5”

private def compactCanonicalFormulaTableSourcePayloadBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 6 :=
  “#0 < #1 + 1” ⋏ compactCanonicalFormulaTableSourcePayloadTail

private theorem compactCanonicalFormulaTable_bShift_payloadBound :
    Rew.bShift
        (‘#0 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 5) =
      (‘#1 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 6) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem compactCanonicalFormulaTableDef_val_eq_outerExists :
    compactCanonicalPackedTokenStreamTableauAtWidthDef.val =
      ∃⁰ compactCanonicalFormulaTableSourcePayloadBody := by
  unfold compactCanonicalPackedTokenStreamTableauAtWidthDef
  change
    compactCanonicalFormulaTableSourcePayloadTail.bexsLTSucc
        (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5) =
      ∃⁰ compactCanonicalFormulaTableSourcePayloadBody
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
  unfold LO.FirstOrder.Semiformula.bexsLT
  unfold compactCanonicalFormulaTableSourcePayloadBody
  rw [compactCanonicalFormulaTable_bShift_payloadBound]
  rfl

private def compactCanonicalFormulaTablePublicTerms
    (tokens : List Nat) : Fin 5 -> ValuationTerm :=
  let width := (compactBinaryNatPayloadBits tokens).length
  ![shortBinaryNumeralTerm (compactAdditivePackedCode tokens),
    shortBinaryNumeralTerm tokens.length,
    shortBinaryNumeralTerm (compactFixedWidthTableCode width tokens),
    shortBinaryNumeralTerm (compactFixedWidthTableCode width
      (compactBinaryNatTokenOffsets tokens)),
    shortBinaryNumeralTerm width]

private def compactCanonicalFormulaTablePayloadTerms
    (tokens : List Nat) : Fin 6 -> ValuationTerm :=
  let width := (compactBinaryNatPayloadBits tokens).length
  ![shortBinaryNumeralTerm (compactBinaryNatPayloadValue tokens),
    shortBinaryNumeralTerm (compactAdditivePackedCode tokens),
    shortBinaryNumeralTerm tokens.length,
    shortBinaryNumeralTerm (compactFixedWidthTableCode width tokens),
    shortBinaryNumeralTerm (compactFixedWidthTableCode width
      (compactBinaryNatTokenOffsets tokens)),
    shortBinaryNumeralTerm width]

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_zero
    (tokens : List Nat) :
    compactCanonicalFormulaTablePayloadTerms tokens 0 =
      shortBinaryNumeralTerm (compactBinaryNatPayloadValue tokens) := rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_one
    (tokens : List Nat) :
    compactCanonicalFormulaTablePayloadTerms tokens 1 =
      shortBinaryNumeralTerm (compactAdditivePackedCode tokens) := rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_two
    (tokens : List Nat) :
    compactCanonicalFormulaTablePayloadTerms tokens 2 =
      shortBinaryNumeralTerm tokens.length := rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_three
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    compactCanonicalFormulaTablePayloadTerms tokens 3 =
      shortBinaryNumeralTerm
        (compactFixedWidthTableCode width tokens) := rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_four
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    compactCanonicalFormulaTablePayloadTerms tokens 4 =
      shortBinaryNumeralTerm
        (compactFixedWidthTableCode width
          (compactBinaryNatTokenOffsets tokens)) := rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_five
    (tokens : List Nat) :
    compactCanonicalFormulaTablePayloadTerms tokens 5 =
      shortBinaryNumeralTerm
        (compactBinaryNatPayloadBits tokens).length := rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_one
    (tokens : List Nat) :
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#1 : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      Rew.bShift (shortBinaryNumeralTerm
        (compactBinaryNatPayloadValue tokens)) := by
  change
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#((0 : Fin 6).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar]
  rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_two
    (tokens : List Nat) :
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      Rew.bShift (shortBinaryNumeralTerm
        (compactAdditivePackedCode tokens)) := by
  change
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#((1 : Fin 6).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar]
  rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_three
    (tokens : List Nat) :
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      Rew.bShift (shortBinaryNumeralTerm tokens.length) := by
  change
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#((2 : Fin 6).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar]
  rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_four
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#4 : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      Rew.bShift (shortBinaryNumeralTerm
        (compactFixedWidthTableCode width tokens)) := by
  change
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#((3 : Fin 6).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar]
  rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_five
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#5 : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      Rew.bShift (shortBinaryNumeralTerm
        (compactFixedWidthTableCode width
          (compactBinaryNatTokenOffsets tokens))) := by
  change
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#((4 : Fin 6).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar]
  rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_six
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#6 : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      Rew.bShift (shortBinaryNumeralTerm width) := by
  change
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q
        (#((5 : Fin 6).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar]
  rfl

private def compactCanonicalFormulaTableRewrittenPayloadBody
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (Rew.subst (compactCanonicalFormulaTablePublicTerms tokens)).q ▹
    (Rewriting.emb (ξ := Nat)
      compactCanonicalFormulaTableSourcePayloadBody)

private theorem compactCanonicalFormulaTableClosedFormula_eq_outerExists
    (tokens : List Nat) :
    compactCanonicalFormulaTableClosedFormula tokens =
      ∃⁰ compactCanonicalFormulaTableRewrittenPayloadBody tokens := by
  unfold compactCanonicalFormulaTableClosedFormula
  rw [compactCanonicalFormulaTableDef_val_eq_outerExists]
  change
    Rew.subst (compactCanonicalFormulaTablePublicTerms tokens) ▹
        (Rewriting.emb (ξ := Nat)
          (∃⁰ compactCanonicalFormulaTableSourcePayloadBody)) =
      ∃⁰ compactCanonicalFormulaTableRewrittenPayloadBody tokens
  simp only [Rewriting.app_exs, Rew.q_emb]
  rfl

private def compactCanonicalFormulaTablePayloadGuard
    (tokens : List Nat) : ArithmeticProposition :=
  let payload := compactBinaryNatPayloadValue tokens
  let code := compactAdditivePackedCode tokens
  “!!(shortBinaryNumeralTerm payload) <
    !!(shortBinaryNumeralTerm code) + 1”

private def compactCanonicalFormulaTableWidthGuard
    (tokens : List Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  let code := compactAdditivePackedCode tokens
  “!!(shortBinaryNumeralTerm width) ≤
    !!(shortBinaryNumeralTerm code)”

private def compactCanonicalFormulaTableSentinelBody
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let code := compactAdditivePackedCode tokens
  let tokenTable := compactFixedWidthTableCode width tokens
  let offsetTable := compactFixedWidthTableCode width
    (compactBinaryNatTokenOffsets tokens)
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm code)) + 1 ∧
    (!expDef #0 !!(Rew.bShift (shortBinaryNumeralTerm width)) ∧
      !!(Rew.bShift (shortBinaryNumeralTerm payload)) < #0 ∧
      !!(Rew.bShift (shortBinaryNumeralTerm code)) =
        !!(Rew.bShift (shortBinaryNumeralTerm payload)) + #0 ∧
      !(compactBinaryNatTokenStreamTableauDef)
        !!(Rew.bShift (shortBinaryNumeralTerm payload))
        !!(Rew.bShift (shortBinaryNumeralTerm width))
        #0
        !!(Rew.bShift (shortBinaryNumeralTerm tokens.length))
        !!(Rew.bShift (shortBinaryNumeralTerm tokenTable))
        !!(Rew.bShift (shortBinaryNumeralTerm offsetTable)))”

private def compactCanonicalFormulaTablePayloadInstantiatedFormula
    (tokens : List Nat) : ArithmeticProposition :=
  compactCanonicalFormulaTablePayloadGuard tokens ⋏
    (compactCanonicalFormulaTableWidthGuard tokens ⋏
      (∃⁰ compactCanonicalFormulaTableSentinelBody tokens))

private theorem compactCanonicalFormulaTable_subst_bShiftTerm
    (term witness : ValuationTerm) :
    Rew.subst ![witness] (Rew.bShift term) = term := by
  calc
    Rew.subst ![witness] (Rew.bShift term) =
        ((Rew.subst ![witness]).comp Rew.bShift) term := by
      rw [Rew.comp_app]
    _ = Rew.id term := by
      rw [Rew.subst_comp_bShift_eq_id]
    _ = term := Rew.id_app term

private theorem compactCanonicalFormulaTable_rewriting_embeddedSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula :
      LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
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
      rw [TransitiveRewriting.comp_app,
        TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem compactCanonicalFormulaTable_rewriting_emb_empty
    {boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty boundArity) :
    Rewriting.emb (ξ := Empty) formula = formula := by
  change
    (Rew.emb : Rew ℒₒᵣ Empty boundArity Empty boundArity) ▹ formula =
      formula
  rw [Rew.emb_eq_id]
  exact ReflectiveRewriting.id_app formula

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_expDef
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q ▹
        (expDef.val ⇜
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6]) =
      (Rewriting.emb (ξ := Nat) expDef.val) ⇜
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm width)] := by
  calc
    _ = (Rew.embSubsts
          (compactCanonicalFormulaTablePayloadTerms tokens)).q ▹
        ((Rewriting.emb (ξ := Empty) expDef.val) ⇜
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6]) := by
      rw [compactCanonicalFormulaTable_rewriting_emb_empty]
    _ = (Rewriting.emb (ξ := Nat) expDef.val) ⇜
        ((Rew.embSubsts
          (compactCanonicalFormulaTablePayloadTerms tokens)).q ∘
            ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6]) :=
      compactCanonicalFormulaTable_rewriting_embeddedSubstitution
        (Rew.embSubsts
          (compactCanonicalFormulaTablePayloadTerms tokens)).q
        expDef.val
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6]
    _ = _ := by
      apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Function.comp_def]
      · intro freeIndex
        rfl

@[simp] private theorem compactCanonicalFormulaTablePayloadTerms_q_tableau
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let offsetTable := compactFixedWidthTableCode width
      (compactBinaryNatTokenOffsets tokens)
    (Rew.embSubsts
        (compactCanonicalFormulaTablePayloadTerms tokens)).q ▹
        (compactBinaryNatTokenStreamTableauDef.val ⇜
          ![(#1 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6,
            #0, #3, #4, #5]) =
      (Rewriting.emb (ξ := Nat)
          compactBinaryNatTokenStreamTableauDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm
            (compactBinaryNatPayloadValue tokens)),
          Rew.bShift (shortBinaryNumeralTerm width),
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm tokens.length),
          Rew.bShift (shortBinaryNumeralTerm tokenTable),
          Rew.bShift (shortBinaryNumeralTerm offsetTable)] := by
  calc
    _ = (Rew.embSubsts
          (compactCanonicalFormulaTablePayloadTerms tokens)).q ▹
        ((Rewriting.emb (ξ := Empty)
          compactBinaryNatTokenStreamTableauDef.val) ⇜
          ![(#1 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6,
            #0, #3, #4, #5]) := by
      rw [compactCanonicalFormulaTable_rewriting_emb_empty]
    _ = (Rewriting.emb (ξ := Nat)
          compactBinaryNatTokenStreamTableauDef.val) ⇜
        ((Rew.embSubsts
          (compactCanonicalFormulaTablePayloadTerms tokens)).q ∘
            ![(#1 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6,
              #0, #3, #4, #5]) :=
      compactCanonicalFormulaTable_rewriting_embeddedSubstitution
        (Rew.embSubsts
          (compactCanonicalFormulaTablePayloadTerms tokens)).q
        compactBinaryNatTokenStreamTableauDef.val
        ![(#1 : LO.FirstOrder.ArithmeticSemiterm Empty 7), #6,
          #0, #3, #4, #5]
    _ = _ := by
      apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Function.comp_def]
      · intro freeIndex
        rfl

private theorem compactCanonicalFormulaTablePayloadRewriting_eq
    (tokens : List Nat) :
    (Rew.subst
        ![shortBinaryNumeralTerm
          (compactBinaryNatPayloadValue tokens)]).comp
        ((Rew.subst
          (compactCanonicalFormulaTablePublicTerms tokens)).q.comp
            (Rew.emb : Rew ℒₒᵣ Empty 6 Nat 6)) =
      Rew.embSubsts (compactCanonicalFormulaTablePayloadTerms tokens) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.comp_app, compactCanonicalFormulaTablePayloadTerms]
    | succ coordinate =>
        simp only [Rew.comp_app, Rew.emb_bvar, Rew.q_bvar_succ,
          Rew.embSubsts_bvar]
        rw [compactCanonicalFormulaTable_subst_bShiftTerm,
          Rew.subst_bvar]
        fin_cases coordinate <;>
          rfl
  · exact Empty.elim coordinate

private theorem compactCanonicalFormulaTableSourcePayloadBody_rewrite
    (tokens : List Nat) :
    Rew.embSubsts (compactCanonicalFormulaTablePayloadTerms tokens) ▹
        compactCanonicalFormulaTableSourcePayloadBody =
      compactCanonicalFormulaTablePayloadInstantiatedFormula tokens := by
  simp [compactCanonicalFormulaTableSourcePayloadBody,
    compactCanonicalFormulaTableSourcePayloadTail,
    compactCanonicalFormulaTablePayloadInstantiatedFormula,
    compactCanonicalFormulaTablePayloadGuard,
    compactCanonicalFormulaTableWidthGuard,
    compactCanonicalFormulaTableSentinelBody,
    LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT,
    LO.FirstOrder.bexs,
    LO.FirstOrder.Semiformula.Operator.lt_def,
    LO.FirstOrder.Semiformula.Operator.le_def,
    LO.FirstOrder.Semiformula.Operator.eq_def,
    Rew.q_bvar_zero, Rew.embSubsts_bvar]

private theorem compactCanonicalFormulaTablePayloadSubstitution_eq
    (tokens : List Nat) :
    (compactCanonicalFormulaTableRewrittenPayloadBody tokens)/[
        shortBinaryNumeralTerm (compactBinaryNatPayloadValue tokens)] =
      compactCanonicalFormulaTablePayloadInstantiatedFormula tokens := by
  calc
    (compactCanonicalFormulaTableRewrittenPayloadBody tokens)/[
        shortBinaryNumeralTerm
          (compactBinaryNatPayloadValue tokens)] =
        ((Rew.subst
            ![shortBinaryNumeralTerm
              (compactBinaryNatPayloadValue tokens)]).comp
          ((Rew.subst
            (compactCanonicalFormulaTablePublicTerms tokens)).q.comp
              (Rew.emb : Rew ℒₒᵣ Empty 6 Nat 6))) ▹
            compactCanonicalFormulaTableSourcePayloadBody := by
      unfold compactCanonicalFormulaTableRewrittenPayloadBody
      rw [TransitiveRewriting.comp_app,
        TransitiveRewriting.comp_app]
    _ = Rew.embSubsts
          (compactCanonicalFormulaTablePayloadTerms tokens) ▹
            compactCanonicalFormulaTableSourcePayloadBody := by
      rw [compactCanonicalFormulaTablePayloadRewriting_eq]
    _ = compactCanonicalFormulaTablePayloadInstantiatedFormula tokens :=
      compactCanonicalFormulaTableSourcePayloadBody_rewrite tokens

private noncomputable def compactCanonicalFormulaTablePayloadGuardCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTablePayloadGuard tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let code := compactAdditivePackedCode tokens
  have hbounds :=
    compactNumericListedDirectCanonicalFormulaTable_internalBounds
      tokens code rfl
  have hpayloadCode : payload ≤ code := by
    simpa only [width, payload, code] using hbounds.2.1
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm payload,
      (‘!!(shortBinaryNumeralTerm code) + 1’ : ValuationTerm)] (by
        change LO.FirstOrder.Semiterm.val ![] zeroValuation
            (shortBinaryNumeralTerm payload) <
          LO.FirstOrder.Semiterm.val ![] zeroValuation
            (shortBinaryNumeralTerm code) + 1
        have hpayloadValue :
            LO.FirstOrder.Semiterm.val ![] zeroValuation
              (shortBinaryNumeralTerm payload) = payload :=
          termValue_shortBinaryNumeralTerm zeroValuation payload
        have hcodeValue :
            LO.FirstOrder.Semiterm.val ![] zeroValuation
              (shortBinaryNumeralTerm code) = code :=
          termValue_shortBinaryNumeralTerm zeroValuation code
        rw [hpayloadValue, hcodeValue]
        exact Nat.lt_succ_of_le hpayloadCode)
  exact .cast (by
    unfold compactCanonicalFormulaTablePayloadGuard
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def compactCanonicalFormulaTableWidthGuardCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableWidthGuard tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let code := compactAdditivePackedCode tokens
  let sentinel := 2 ^ width
  have hbounds :=
    compactNumericListedDirectCanonicalFormulaTable_internalBounds
      tokens code rfl
  have hsentinelCode : sentinel ≤ code := by
    simpa only [width, code, sentinel] using hbounds.2.2.1
  have hwidthCode : width < code :=
    width.lt_two_pow_self.trans_le hsentinelCode
  let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm width, shortBinaryNumeralTerm code] (by
      change LO.FirstOrder.Semiterm.val ![] zeroValuation
          (shortBinaryNumeralTerm width) <
        LO.FirstOrder.Semiterm.val ![] zeroValuation
          (shortBinaryNumeralTerm code)
      have hwidthValue : LO.FirstOrder.Semiterm.val ![] zeroValuation
          (shortBinaryNumeralTerm width) = width :=
        termValue_shortBinaryNumeralTerm zeroValuation width
      have hcodeValue : LO.FirstOrder.Semiterm.val ![] zeroValuation
          (shortBinaryNumeralTerm code) = code :=
        termValue_shortBinaryNumeralTerm zeroValuation code
      rw [hwidthValue, hcodeValue]
      exact hwidthCode)
  let direct := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![shortBinaryNumeralTerm width, shortBinaryNumeralTerm code]) strict
  exact .cast (by
    unfold compactCanonicalFormulaTableWidthGuard
    exact (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm) direct

private theorem compactCanonicalFormulaTableSentinelBody_sigmaZero
    (tokens : List Nat) :
    Hierarchy Polarity.sigma 0
      (compactCanonicalFormulaTableSentinelBody tokens) := by
  simp [compactCanonicalFormulaTableSentinelBody]

private theorem compactCanonicalFormulaTableSentinelBody_truth
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let sentinel := 2 ^ width
    formulaValue zeroValuation
      ((compactCanonicalFormulaTableSentinelBody tokens)/[
        shortBinaryNumeralTerm sentinel]) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ width
  let code := compactAdditivePackedCode tokens
  let tokenTable := compactFixedWidthTableCode width tokens
  let offsetTable := compactFixedWidthTableCode width
    (compactBinaryNatTokenOffsets tokens)
  have hbounds :=
    compactNumericListedDirectCanonicalFormulaTable_internalBounds
      tokens code rfl
  have hsentinelCode : sentinel ≤ code := by
    simpa only [width, code, sentinel] using hbounds.2.2.1
  have hpayloadSentinel : payload < sentinel := by
    exact natOfBitsList_lt_two_pow_length
      (compactBinaryNatPayloadBits tokens)
  have hcode : code = payload + sentinel := by
    change packBinaryString (compactBinaryNatPayloadBits tokens) =
      compactBinaryNatPayloadValue tokens + 2 ^ width
    exact packBinaryString_eq_payload_add_sentinel
      (compactBinaryNatPayloadBits tokens)
  have htableau : CompactBinaryNatTokenStreamTableau payload width sentinel
      tokens.length tokenTable offsetTable := by
    simpa only [payload, width, sentinel, tokenTable, offsetTable] using
      compactBinaryNatTokenStreamTableau_canonical tokens
  have hcodeValue :
      LO.FirstOrder.Semiterm.val ![] zeroValuation
        (shortBinaryNumeralTerm code) = code := by
    exact termValue_shortBinaryNumeralTerm zeroValuation code
  have hwidthValue :
      LO.FirstOrder.Semiterm.val ![] zeroValuation
        (shortBinaryNumeralTerm width) = width := by
    exact termValue_shortBinaryNumeralTerm zeroValuation width
  have hpayloadValue :
      LO.FirstOrder.Semiterm.val ![] zeroValuation
        (shortBinaryNumeralTerm payload) = payload := by
    exact termValue_shortBinaryNumeralTerm zeroValuation payload
  let tableauTerms : Fin 6 ->
      LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ![Rew.bShift (shortBinaryNumeralTerm payload),
      Rew.bShift (shortBinaryNumeralTerm width),
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm tokens.length),
      Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm offsetTable)]
  have htableauValues :
      (LO.FirstOrder.Semiterm.val ![sentinel] zeroValuation ∘
        tableauTerms) =
        ![payload, width, sentinel, tokens.length, tokenTable,
          offsetTable] := by
    funext coordinate
    fin_cases coordinate
    · simpa [tableauTerms, termValue_shortBinaryNumeralTerm] using
        termValue_bShift sentinel zeroValuation
          (shortBinaryNumeralTerm payload)
    · simpa [tableauTerms, termValue_shortBinaryNumeralTerm] using
        termValue_bShift sentinel zeroValuation
          (shortBinaryNumeralTerm width)
    · rfl
    · simpa [tableauTerms, termValue_shortBinaryNumeralTerm] using
        termValue_bShift sentinel zeroValuation
          (shortBinaryNumeralTerm tokens.length)
    · simpa [tableauTerms, termValue_shortBinaryNumeralTerm] using
        termValue_bShift sentinel zeroValuation
          (shortBinaryNumeralTerm tokenTable)
    · simpa [tableauTerms, termValue_shortBinaryNumeralTerm] using
        termValue_bShift sentinel zeroValuation
          (shortBinaryNumeralTerm offsetTable)
  have htableauEval :
      LO.FirstOrder.Semiformula.Eval
        (LO.FirstOrder.Semiterm.val ![sentinel] zeroValuation ∘
          tableauTerms)
        Empty.elim compactBinaryNatTokenStreamTableauDef.val := by
    rw [htableauValues]
    simpa using
      (compactBinaryNatTokenStreamTableauDef_spec payload width sentinel
        tokens.length tokenTable offsetTable).2 htableau
  apply (formulaValue_shortBinarySubstitution zeroValuation
    (compactCanonicalFormulaTableSentinelBody tokens) sentinel).mpr
  simp [compactCanonicalFormulaTableSentinelBody,
    LO.FirstOrder.Semiformula.eval_substs,
    LO.FirstOrder.Semiformula.eval_emb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcodeValue]
    exact hsentinelCode
  · rw [← compactBinaryNatPayloadBits_length tokens]
    rw [hwidthValue]
  · rw [hpayloadValue]
    exact hpayloadSentinel
  · rw [hcodeValue, hpayloadValue]
    exact hcode
  · rw [← compactBinaryNatPayloadBits_length tokens]
    change LO.FirstOrder.Semiformula.Eval
      (LO.FirstOrder.Semiterm.val ![sentinel] zeroValuation ∘
        tableauTerms)
      Empty.elim compactBinaryNatTokenStreamTableauDef.val
    exact htableauEval

private def compactCanonicalFormulaTableSentinelGuard
    (tokens : List Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  let sentinel := 2 ^ width
  let code := compactAdditivePackedCode tokens
  “!!(shortBinaryNumeralTerm sentinel) <
    !!(shortBinaryNumeralTerm code) + 1”

private def compactCanonicalFormulaTableSentinelExponential
    (tokens : List Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  exponentialAtValuationFormula
    (shortBinaryNumeralTerm (2 ^ width))
    (shortBinaryNumeralTerm width)

private def compactCanonicalFormulaTableSentinelPayloadGuard
    (tokens : List Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  “!!(shortBinaryNumeralTerm payload) <
    !!(shortBinaryNumeralTerm (2 ^ width))”

private def compactCanonicalFormulaTableSentinelCodeEquation
    (tokens : List Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let code := compactAdditivePackedCode tokens
  “!!(shortBinaryNumeralTerm code) =
    !!(shortBinaryNumeralTerm payload) +
      !!(shortBinaryNumeralTerm (2 ^ width))”

private def compactCanonicalFormulaTableSentinelTableau
    (tokens : List Nat) : ArithmeticProposition :=
  let width := (compactBinaryNatPayloadBits tokens).length
  compactBinaryNatTokenStreamTableauClosedFormula
    (compactBinaryNatPayloadValue tokens) width (2 ^ width) tokens.length
    (compactFixedWidthTableCode width tokens)
    (compactFixedWidthTableCode width (compactBinaryNatTokenOffsets tokens))

private def compactCanonicalFormulaTableSentinelSourceGuard
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  let code := compactAdditivePackedCode tokens
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm code)) + 1”

private def compactCanonicalFormulaTableSentinelSourceExponential
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  let width := (compactBinaryNatPayloadBits tokens).length
  (Rewriting.emb (ξ := Nat) expDef.val) ⇜
    ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm width)]

private def compactCanonicalFormulaTableSentinelSourcePayloadGuard
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  let payload := compactBinaryNatPayloadValue tokens
  “!!(Rew.bShift (shortBinaryNumeralTerm payload)) < #0”

private def compactCanonicalFormulaTableSentinelSourceCodeEquation
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  let payload := compactBinaryNatPayloadValue tokens
  let code := compactAdditivePackedCode tokens
  “!!(Rew.bShift (shortBinaryNumeralTerm code)) =
    !!(Rew.bShift (shortBinaryNumeralTerm payload)) + #0”

private def compactCanonicalFormulaTableSentinelSourceTableau
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let tokenTable := compactFixedWidthTableCode width tokens
  let offsetTable := compactFixedWidthTableCode width
    (compactBinaryNatTokenOffsets tokens)
  (Rewriting.emb (ξ := Nat)
      compactBinaryNatTokenStreamTableauDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm payload),
      Rew.bShift (shortBinaryNumeralTerm width),
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm tokens.length),
      Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm offsetTable)]

private def compactCanonicalFormulaTableSentinelSourceDecomposed
    (tokens : List Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  compactCanonicalFormulaTableSentinelSourceGuard tokens ⋏
    (compactCanonicalFormulaTableSentinelSourceExponential tokens ⋏
      (compactCanonicalFormulaTableSentinelSourcePayloadGuard tokens ⋏
        (compactCanonicalFormulaTableSentinelSourceCodeEquation tokens ⋏
          compactCanonicalFormulaTableSentinelSourceTableau tokens)))

private theorem compactCanonicalFormulaTableSentinelBody_eq_sourceDecomposed
    (tokens : List Nat) :
    compactCanonicalFormulaTableSentinelBody tokens =
      compactCanonicalFormulaTableSentinelSourceDecomposed tokens := by
  rfl

private def compactCanonicalFormulaTableSentinelInstantiatedFormula
    (tokens : List Nat) : ArithmeticProposition :=
  compactCanonicalFormulaTableSentinelGuard tokens ⋏
    (compactCanonicalFormulaTableSentinelExponential tokens ⋏
      (compactCanonicalFormulaTableSentinelPayloadGuard tokens ⋏
        (compactCanonicalFormulaTableSentinelCodeEquation tokens ⋏
          compactCanonicalFormulaTableSentinelTableau tokens)))

private theorem compactCanonicalFormulaTableSentinelTableauSubstitution_eq
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let sentinel := 2 ^ width
    (compactCanonicalFormulaTableSentinelSourceTableau tokens)/[
        shortBinaryNumeralTerm sentinel] =
      compactCanonicalFormulaTableSentinelTableau tokens := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ width
  let tokenTable := compactFixedWidthTableCode width tokens
  let offsetTable := compactFixedWidthTableCode width
    (compactBinaryNatTokenOffsets tokens)
  let bodyTerms : Fin 6 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ![Rew.bShift (shortBinaryNumeralTerm payload),
      Rew.bShift (shortBinaryNumeralTerm width),
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm tokens.length),
      Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm offsetTable)]
  let closedTerms : Fin 6 -> ValuationTerm :=
    ![shortBinaryNumeralTerm payload,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm sentinel,
      shortBinaryNumeralTerm tokens.length,
      shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm offsetTable]
  change Rew.subst ![shortBinaryNumeralTerm sentinel] ▹
      ((Rewriting.emb (ξ := Nat)
          compactBinaryNatTokenStreamTableauDef.val) ⇜ bodyTerms) =
    (Rewriting.emb (ξ := Nat)
        compactBinaryNatTokenStreamTableauDef.val) ⇜ closedTerms
  calc
    _ = (Rewriting.emb (ξ := Nat)
          compactBinaryNatTokenStreamTableauDef.val) ⇜
        (Rew.subst ![shortBinaryNumeralTerm sentinel] ∘ bodyTerms) :=
      compactCanonicalFormulaTable_rewriting_embeddedSubstitution
        (Rew.subst ![shortBinaryNumeralTerm sentinel])
        compactBinaryNatTokenStreamTableauDef.val bodyTerms
    _ = _ := by
      congr 1
      funext coordinate
      fin_cases coordinate <;>
        simp [bodyTerms, closedTerms,
          compactCanonicalFormulaTable_subst_bShiftTerm,
          Function.comp_def]

private theorem compactCanonicalFormulaTableSentinelSubstitution_eq
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let sentinel := 2 ^ width
    (compactCanonicalFormulaTableSentinelBody tokens)/[
        shortBinaryNumeralTerm sentinel] =
      compactCanonicalFormulaTableSentinelInstantiatedFormula tokens := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let sentinel := 2 ^ width
  change (compactCanonicalFormulaTableSentinelBody tokens)/[
      shortBinaryNumeralTerm sentinel] =
    compactCanonicalFormulaTableSentinelInstantiatedFormula tokens
  have hguard :
      (compactCanonicalFormulaTableSentinelSourceGuard tokens)/[
          shortBinaryNumeralTerm sentinel] =
        compactCanonicalFormulaTableSentinelGuard tokens := by
    unfold compactCanonicalFormulaTableSentinelSourceGuard
    unfold compactCanonicalFormulaTableSentinelGuard
    simp [compactCanonicalFormulaTable_subst_bShiftTerm,
      LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_one,
      LO.FirstOrder.Semiterm.Operator.Add.term_eq,
      LO.FirstOrder.Semiterm.Operator.One.term_eq,
      Rew.func, Rew.comp_app, Matrix.fun_eq_vec_two]
    rw [← compactBinaryNatPayloadBits_length tokens]
  have hexponential :
      (compactCanonicalFormulaTableSentinelSourceExponential tokens)/[
          shortBinaryNumeralTerm sentinel] =
        compactCanonicalFormulaTableSentinelExponential tokens := by
    let bodyTerms : Fin 2 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
        Rew.bShift (shortBinaryNumeralTerm width)]
    let closedTerms : Fin 2 -> ValuationTerm :=
      ![shortBinaryNumeralTerm sentinel, shortBinaryNumeralTerm width]
    change Rew.subst ![shortBinaryNumeralTerm sentinel] ▹
        ((Rewriting.emb (ξ := Nat) expDef.val) ⇜ bodyTerms) =
      (Rewriting.emb (ξ := Nat) expDef.val) ⇜ closedTerms
    calc
      _ = (Rewriting.emb (ξ := Nat) expDef.val) ⇜
          (Rew.subst ![shortBinaryNumeralTerm sentinel] ∘ bodyTerms) :=
        compactCanonicalFormulaTable_rewriting_embeddedSubstitution
          (Rew.subst ![shortBinaryNumeralTerm sentinel]) expDef.val bodyTerms
      _ = _ := by
        congr 1
        funext coordinate
        fin_cases coordinate <;>
          simp [bodyTerms, closedTerms,
            compactCanonicalFormulaTable_subst_bShiftTerm,
            Function.comp_def]
  have hpayload :
      (compactCanonicalFormulaTableSentinelSourcePayloadGuard tokens)/[
          shortBinaryNumeralTerm sentinel] =
        compactCanonicalFormulaTableSentinelPayloadGuard tokens := by
    unfold compactCanonicalFormulaTableSentinelSourcePayloadGuard
    unfold compactCanonicalFormulaTableSentinelPayloadGuard
    simp [compactCanonicalFormulaTable_subst_bShiftTerm,
      Rew.comp_app, Matrix.fun_eq_vec_two]
    rw [← compactBinaryNatPayloadBits_length tokens]
  have hcode :
      (compactCanonicalFormulaTableSentinelSourceCodeEquation tokens)/[
          shortBinaryNumeralTerm sentinel] =
        compactCanonicalFormulaTableSentinelCodeEquation tokens := by
    unfold compactCanonicalFormulaTableSentinelSourceCodeEquation
    unfold compactCanonicalFormulaTableSentinelCodeEquation
    simp [compactCanonicalFormulaTable_subst_bShiftTerm,
      LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.Add.term_eq,
      Rew.func, Rew.comp_app, Matrix.fun_eq_vec_two]
    rw [← compactBinaryNatPayloadBits_length tokens]
  have htableau :
      (compactCanonicalFormulaTableSentinelSourceTableau tokens)/[
          shortBinaryNumeralTerm sentinel] =
        compactCanonicalFormulaTableSentinelTableau tokens := by
    exact compactCanonicalFormulaTableSentinelTableauSubstitution_eq tokens
  rw [compactCanonicalFormulaTableSentinelBody_eq_sourceDecomposed]
  unfold compactCanonicalFormulaTableSentinelSourceDecomposed
  unfold compactCanonicalFormulaTableSentinelInstantiatedFormula
  simp only [LogicalConnective.HomClass.map_and]
  exact congrArg₂ (fun left right => left ⋏ right) hguard
    (congrArg₂ (fun left right => left ⋏ right) hexponential
      (congrArg₂ (fun left right => left ⋏ right) hpayload
        (congrArg₂ (fun left right => left ⋏ right) hcode htableau)))

private noncomputable def compactCanonicalFormulaTableSentinelGuardCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableSentinelGuard tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let sentinel := 2 ^ width
  let code := compactAdditivePackedCode tokens
  have hbounds :=
    compactNumericListedDirectCanonicalFormulaTable_internalBounds
      tokens code rfl
  have hsentinelCode : sentinel <= code := by
    simpa only [width, sentinel, code] using hbounds.2.2.1
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm sentinel,
      (‘!!(shortBinaryNumeralTerm code) + 1’ : ValuationTerm)] (by
        change termValue zeroValuation (shortBinaryNumeralTerm sentinel) <
          termValue zeroValuation
            (‘!!(shortBinaryNumeralTerm code) + 1’ : ValuationTerm)
        simpa [compactCanonicalFormulaTable_termValue_arithmeticAdd,
          compactCanonicalFormulaTable_termValue_arithmeticOne,
          termValue_shortBinaryNumeralTerm] using
            Nat.lt_succ_of_le hsentinelCode)
  exact .cast (by
    unfold compactCanonicalFormulaTableSentinelGuard
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def
    compactCanonicalFormulaTableSentinelExponentialCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableSentinelExponential tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  exact .exponential zeroValuation
    (shortBinaryNumeralTerm (2 ^ width))
    (shortBinaryNumeralTerm width) (by
      simp [termValue_shortBinaryNumeralTerm])

private noncomputable def
    compactCanonicalFormulaTableSentinelPayloadGuardCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableSentinelPayloadGuard tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ width
  have hpayloadSentinel : payload < sentinel := by
    exact natOfBitsList_lt_two_pow_length
      (compactBinaryNatPayloadBits tokens)
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm payload,
      shortBinaryNumeralTerm sentinel] (by
        change termValue zeroValuation (shortBinaryNumeralTerm payload) <
          termValue zeroValuation (shortBinaryNumeralTerm sentinel)
        simpa [termValue_shortBinaryNumeralTerm] using hpayloadSentinel)
  exact .cast (by
    unfold compactCanonicalFormulaTableSentinelPayloadGuard
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def
    compactCanonicalFormulaTableSentinelCodeEquationCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableSentinelCodeEquation tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ width
  let code := compactAdditivePackedCode tokens
  have hcode : code = payload + sentinel := by
    change packBinaryString (compactBinaryNatPayloadBits tokens) =
      compactBinaryNatPayloadValue tokens + 2 ^ width
    exact packBinaryString_eq_payload_add_sentinel
      (compactBinaryNatPayloadBits tokens)
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm payload) +
      !!(shortBinaryNumeralTerm sentinel)’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm code, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm code) =
        termValue zeroValuation rightTerm
      simpa [rightTerm,
        compactCanonicalFormulaTable_termValue_arithmeticAdd,
        termValue_shortBinaryNumeralTerm] using hcode)
  exact .cast (by
    unfold compactCanonicalFormulaTableSentinelCodeEquation rightTerm
    exact (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm) direct

private noncomputable def compactCanonicalFormulaTableSentinelCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableSentinelInstantiatedFormula tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let code := compactAdditivePackedCode tokens
  let tableau :=
    compactBinaryNatTokenStreamTableauCanonicalExplicitHybridCertificate
      tokens code rfl
  exact .conjunction
    (compactCanonicalFormulaTableSentinelGuardCertificate tokens)
    (.conjunction
      (compactCanonicalFormulaTableSentinelExponentialCertificate tokens)
      (.conjunction
        (compactCanonicalFormulaTableSentinelPayloadGuardCertificate tokens)
        (.conjunction
          (compactCanonicalFormulaTableSentinelCodeEquationCertificate tokens)
          (by simpa [compactCanonicalFormulaTableSentinelTableau, width]
            using tableau))))

/-- Fully explicit certificate: payload, sentinel, and every token-stream row
witness are concrete; no Sigma-zero truth fallback remains on this route. -/
noncomputable def compactCanonicalFormulaTableExplicitCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableClosedFormula tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ width
  rw [compactCanonicalFormulaTableClosedFormula_eq_outerExists]
  refine .existsWitness
    (compactCanonicalFormulaTableRewrittenPayloadBody tokens) payload ?_
  let sentinelTerminal :=
    CheckedHybridValuationBoundedFormulaCertificate.cast
      (compactCanonicalFormulaTableSentinelSubstitution_eq tokens).symm
      (compactCanonicalFormulaTableSentinelCertificate tokens)
  let sentinelCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      (compactCanonicalFormulaTableSentinelBody tokens) sentinel
      sentinelTerminal
  let source := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactCanonicalFormulaTablePayloadGuardCertificate tokens)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactCanonicalFormulaTableWidthGuardCertificate tokens)
      sentinelCertificate)
  exact .cast
    (compactCanonicalFormulaTablePayloadSubstitution_eq tokens).symm source

/-- Fully explicit canonical-table certificate transported to a separately
named code already proved equal to the canonical packed code. -/
noncomputable def compactCanonicalFormulaTableExplicitCertificateAtCode
    (tokens : List Nat) (code : Nat)
    (hcode : code = compactAdditivePackedCode tokens) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableClosedFormulaAtCode tokens code) :=
  .cast
    (compactCanonicalFormulaTableClosedFormulaAtCode_eq
      tokens code hcode).symm
    (compactCanonicalFormulaTableExplicitCertificate tokens)

/-- Empty-context PA derivation compiled from the fully explicit route. -/
noncomputable def compileCompactCanonicalFormulaTableExplicitContext
    (tokens : List Nat) :
    CertifiedPAContextProof ∅
      (compactCanonicalFormulaTableClosedFormula tokens) := by
  let raw := (compactCanonicalFormulaTableExplicitCertificate tokens).compile
  have hcontext :
      valuationContext
          (compactCanonicalFormulaTableClosedFormula tokens).freeVariables
          zeroValuation = ∅ := by
    rw [compactCanonicalFormulaTableClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

theorem compileCompactCanonicalFormulaTableExplicitContext_payloadLength_eq
    (tokens : List Nat) :
    (compileCompactCanonicalFormulaTableExplicitContext tokens).payloadLength =
      (compactCanonicalFormulaTableExplicitCertificate tokens).compile.payloadLength := by
  unfold compileCompactCanonicalFormulaTableExplicitContext
  simp only [CertifiedPAContextProof.castContext_payloadLength]

/--
Only the outer payload/sentinel prefix is intended to be explicit here.  The
remaining Sigma-zero body may still select token-row witnesses automatically.
-/
noncomputable def compactCanonicalFormulaTableOuterWitnessCertificate
    (tokens : List Nat) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactCanonicalFormulaTableClosedFormula tokens) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ width
  rw [compactCanonicalFormulaTableClosedFormula_eq_outerExists]
  refine .existsWitness
    (compactCanonicalFormulaTableRewrittenPayloadBody tokens) payload ?_
  let terminal := ofSigmaZeroTruth
    ((compactCanonicalFormulaTableSentinelBody tokens)/[
      shortBinaryNumeralTerm sentinel])
    ((compactCanonicalFormulaTableSentinelBody_sigmaZero tokens).rew
      (Rew.subst ![shortBinaryNumeralTerm sentinel]))
    zeroValuation
    (compactCanonicalFormulaTableSentinelBody_truth tokens)
  let sentinelCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      (compactCanonicalFormulaTableSentinelBody tokens) sentinel terminal
  let source := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactCanonicalFormulaTablePayloadGuardCertificate tokens)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactCanonicalFormulaTableWidthGuardCertificate tokens)
      sentinelCertificate)
  -- Both outer witnesses are fixed in `source`.  The terminal fallback still
  -- has to be replaced to expose token/offset/next choices in every row.
  exact .cast
    (compactCanonicalFormulaTablePayloadSubstitution_eq tokens).symm source

/-- Compilation of the outer-witness certificate in its checked context. -/
noncomputable def compileCompactCanonicalFormulaTableOuterWitnessContext
    (tokens : List Nat) :
    CertifiedPAContextProof ∅
      (compactCanonicalFormulaTableClosedFormula tokens) := by
  let raw :=
    (compactCanonicalFormulaTableOuterWitnessCertificate tokens).compile
  have hcontext :
      valuationContext
          (compactCanonicalFormulaTableClosedFormula tokens).freeVariables
          zeroValuation = ∅ := by
    rw [compactCanonicalFormulaTableClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

theorem compileCompactCanonicalFormulaTableOuterWitnessContext_payloadLength_eq
    (tokens : List Nat) :
    (compileCompactCanonicalFormulaTableOuterWitnessContext tokens).payloadLength =
      (compactCanonicalFormulaTableOuterWitnessCertificate tokens).compile.payloadLength := by
  unfold compileCompactCanonicalFormulaTableOuterWitnessContext
  simp only [CertifiedPAContextProof.castContext_payloadLength]

/-- A genuine checked PA derivation of the canonical closed tableau formula. -/
noncomputable def compileCompactCanonicalFormulaTableOuterWitness
    (tokens : List Nat) :
    CertifiedPAProof
      (compactCanonicalFormulaTableClosedFormula tokens) :=
  certifiedContextProofOfEmpty
    (compileCompactCanonicalFormulaTableOuterWitnessContext tokens)

private theorem certifiedContextProofOfEmpty_payloadLength_eq
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof ∅ formula) :
    (certifiedContextProofOfEmpty proof).payloadLength =
      proof.payloadLength := by
  rw [CertifiedPAProof.payloadLength_eq]
  rfl

/-- Checked PA proof produced by the fully explicit canonical route. -/
noncomputable def compileCompactCanonicalFormulaTableExplicit
    (tokens : List Nat) :
    CertifiedPAProof (compactCanonicalFormulaTableClosedFormula tokens) :=
  certifiedContextProofOfEmpty
    (compileCompactCanonicalFormulaTableExplicitContext tokens)

theorem compileCompactCanonicalFormulaTableExplicit_payloadLength_eq_context
    (tokens : List Nat) :
    (compileCompactCanonicalFormulaTableExplicit tokens).payloadLength =
      (compileCompactCanonicalFormulaTableExplicitContext tokens).payloadLength := by
  unfold compileCompactCanonicalFormulaTableExplicit
  exact certifiedContextProofOfEmpty_payloadLength_eq _

theorem compileCompactCanonicalFormulaTableExplicit_publicVerifier_eq_true
    (tokens : List Nat) :
    compactNumericListedPublicVerifier
        (compileCompactCanonicalFormulaTableExplicit tokens).code
        (compactFormulaCode
          (compactCanonicalFormulaTableClosedFormula tokens)) = true := by
  rw [compactNumericListedPublicVerifier_pointwise]
  exact (compileCompactCanonicalFormulaTableExplicit tokens).verifier_eq_true

noncomputable def compactCanonicalFormulaTableExplicitStructuralResource
    (tokens : List Nat) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactCanonicalFormulaTableExplicitCertificate tokens)

theorem compileCompactCanonicalFormulaTableExplicit_payloadLength_le_structure
    (tokens : List Nat) :
    (compileCompactCanonicalFormulaTableExplicit tokens).payloadLength <=
      compactCanonicalFormulaTableExplicitStructuralResource tokens := by
  rw [compileCompactCanonicalFormulaTableExplicit_payloadLength_eq_context]
  rw [compileCompactCanonicalFormulaTableExplicitContext_payloadLength_eq]
  simpa only [compactCanonicalFormulaTableExplicitStructuralResource] using
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      (compactCanonicalFormulaTableExplicitCertificate tokens)

theorem compileCompactCanonicalFormulaTableOuterWitness_payloadLength_eq_context
    (tokens : List Nat) :
    (compileCompactCanonicalFormulaTableOuterWitness tokens).payloadLength =
      (compileCompactCanonicalFormulaTableOuterWitnessContext tokens).payloadLength := by
  unfold compileCompactCanonicalFormulaTableOuterWitness
  exact certifiedContextProofOfEmpty_payloadLength_eq _

/-- The public numeric verifier accepts the compiled outer-witness proof. -/
theorem compileCompactCanonicalFormulaTableOuterWitness_publicVerifier_eq_true
    (tokens : List Nat) :
    compactNumericListedPublicVerifier
        (compileCompactCanonicalFormulaTableOuterWitness tokens).code
        (compactFormulaCode
          (compactCanonicalFormulaTableClosedFormula tokens)) = true := by
  rw [compactNumericListedPublicVerifier_pointwise]
  exact
    (compileCompactCanonicalFormulaTableOuterWitness tokens).verifier_eq_true

/--
Proof-free structural resource obtained by recursion over this concrete hybrid
certificate.  This is intentionally not presented as a public polynomial.
-/
noncomputable def compactCanonicalFormulaTableOuterWitnessStructuralResource
    (tokens : List Nat) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactCanonicalFormulaTableOuterWitnessCertificate tokens)

/-- The compiled payload is bounded without taking its length as a premise. -/
theorem compileCompactCanonicalFormulaTableOuterWitness_payloadLength_le_structure
    (tokens : List Nat) :
    (compileCompactCanonicalFormulaTableOuterWitness tokens).payloadLength <=
      compactCanonicalFormulaTableOuterWitnessStructuralResource tokens := by
  rw [compileCompactCanonicalFormulaTableOuterWitness_payloadLength_eq_context]
  rw [compileCompactCanonicalFormulaTableOuterWitnessContext_payloadLength_eq]
  simpa only [compactCanonicalFormulaTableOuterWitnessStructuralResource] using
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      (compactCanonicalFormulaTableOuterWitnessCertificate tokens)

#print axioms compactCanonicalFormulaTableExplicitCertificate
#print axioms compactCanonicalFormulaTableExplicitCertificateAtCode
#print axioms compileCompactCanonicalFormulaTableExplicit
#print axioms
  compileCompactCanonicalFormulaTableExplicit_publicVerifier_eq_true
#print axioms
  compileCompactCanonicalFormulaTableExplicit_payloadLength_le_structure
#print axioms compactCanonicalFormulaTableOuterWitnessCertificate
#print axioms compileCompactCanonicalFormulaTableOuterWitness
#print axioms
  compileCompactCanonicalFormulaTableOuterWitness_publicVerifier_eq_true
#print axioms
  compileCompactCanonicalFormulaTableOuterWitness_payloadLength_le_structure

end FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate
