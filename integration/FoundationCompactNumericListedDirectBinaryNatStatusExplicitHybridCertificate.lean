import integration.FoundationCompactNumericListedDirectBinaryNatStatusCases
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

/-!
# Explicit hybrid certificates for binary-Nat parser status tags

The running certificate preserves the original unary `0` term.  The completed
prefix installs its intermediate cursor explicitly and preserves both unary
`1` terms from the source formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def boundedWitnessGuardCertificate
    (value bound : Nat) (hvalue : value ≤ bound) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm value) <
        !!(shortBinaryNumeralTerm bound) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm value, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm value) <
        termValue zeroValuation rightTerm
      simp only [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne]
      omega)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

noncomputable def closedLtCertificate
    (left right : Nat) (hlt : left < right) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) <
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

noncomputable def successorEqualityCertificate
    (left right : Nat) (hsuccessor : right = left + 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm right) =
        !!(shortBinaryNumeralTerm left) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm left) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm right, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm right) =
        termValue zeroValuation rightTerm
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne] using hsuccessor)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

def compactBinaryNatRunningStatusSliceClosedFormula
    (tokenTable width tokenCount start finish : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactBinaryNatRunningStatusSliceDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish]

theorem compactBinaryNatRunningStatusSliceClosedFormula_alignment
    (tokenTable width tokenCount start finish : Nat) :
    compactBinaryNatRunningStatusSliceClosedFormula
        tokenTable width tokenCount start finish =
      compactAdditiveTokenCellAtValuationFormula
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm start)
        (‘0’ : ValuationTerm)
        (shortBinaryNumeralTerm finish) := by
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactBinaryNatRunningStatusSliceDef
  unfold compactAdditiveTokenCellAtValuationFormula
  unfold compactAdditiveTokenCellDef
  simp [← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount start finish : Nat)
    (hgraph : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish) :
    HybridCertificate
      (compactBinaryNatRunningStatusSliceClosedFormula
        tokenTable width tokenCount start finish) := by
  let direct := compactAdditiveTokenCellAtValuationExplicitHybridCertificate
    (shortBinaryNumeralTerm tokenTable)
    (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm start)
    (‘0’ : ValuationTerm)
    (shortBinaryNumeralTerm finish) (by
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticZero,
        CompactBinaryNatRunningStatusSlice,
        FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
        using hgraph)
  exact .cast
    (compactBinaryNatRunningStatusSliceClosedFormula_alignment
      tokenTable width tokenCount start finish).symm direct

def compactBinaryNatFailedStatusSliceClosedFormula
    (tokenTable width tokenCount start finish : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactBinaryNatFailedStatusSliceDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish]

def compactBinaryNatFailedStatusSliceWitnessBody
    (tokenTable width tokenCount start finish : Nat) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (“!!(Rew.bShift (shortBinaryNumeralTerm start)) <
        !!(Rew.bShift (shortBinaryNumeralTerm tokenCount))” ⋏
      (“#0 = !!(Rew.bShift (shortBinaryNumeralTerm start)) + 1” ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
            Rew.bShift (shortBinaryNumeralTerm width),
            Rew.bShift (shortBinaryNumeralTerm start),
            Rew.bShift (‘1’ : ValuationTerm)]) ⋏
          (“#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount))” ⋏
            (“!!(Rew.bShift (shortBinaryNumeralTerm finish)) =
                #0 + 1” ⋏
              ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
                ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
                  Rew.bShift (shortBinaryNumeralTerm width),
                  (#0 : ArithmeticSemiterm Nat 1),
                  Rew.bShift (‘0’ : ValuationTerm)]))))))

theorem compactBinaryNatFailedStatusSliceClosedFormula_alignment
    (tokenTable width tokenCount start finish : Nat) :
    compactBinaryNatFailedStatusSliceClosedFormula
        tokenTable width tokenCount start finish =
      ∃⁰ compactBinaryNatFailedStatusSliceWitnessBody
        tokenTable width tokenCount start finish := by
  unfold compactBinaryNatFailedStatusSliceClosedFormula
  unfold compactBinaryNatFailedStatusSliceWitnessBody
  unfold compactBinaryNatFailedStatusSliceDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactBinaryNatFailedStatusSliceWitnessBody_substitution_alignment
    (tokenTable width tokenCount start finish innerStart : Nat) :
    (compactBinaryNatFailedStatusSliceWitnessBody
      tokenTable width tokenCount start finish)/[
        shortBinaryNumeralTerm innerStart] =
      (“!!(shortBinaryNumeralTerm innerStart) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
        (“!!(shortBinaryNumeralTerm start) <
            !!(shortBinaryNumeralTerm tokenCount)” ⋏
          (“!!(shortBinaryNumeralTerm innerStart) =
              !!(shortBinaryNumeralTerm start) + 1” ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm tokenTable)
                (shortBinaryNumeralTerm width)
                (shortBinaryNumeralTerm start)
                (‘1’ : ValuationTerm) ⋏
              (“!!(shortBinaryNumeralTerm innerStart) <
                  !!(shortBinaryNumeralTerm tokenCount)” ⋏
                (“!!(shortBinaryNumeralTerm finish) =
                    !!(shortBinaryNumeralTerm innerStart) + 1” ⋏
                  compactFixedWidthEntryAtValuationFormula
                    (shortBinaryNumeralTerm tokenTable)
                    (shortBinaryNumeralTerm width)
                    (shortBinaryNumeralTerm innerStart)
                    (‘0’ : ValuationTerm))))))) := by
  unfold compactBinaryNatFailedStatusSliceWitnessBody
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app, Rew.subst_bvar]
  constructor
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def
    compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate
    (tokenTable width tokenCount start finish innerStart : Nat)
    (hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 0 finish) :
    HybridCertificate
      (“!!(shortBinaryNumeralTerm innerStart) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
        (“!!(shortBinaryNumeralTerm start) <
            !!(shortBinaryNumeralTerm tokenCount)” ⋏
          (“!!(shortBinaryNumeralTerm innerStart) =
              !!(shortBinaryNumeralTerm start) + 1” ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm tokenTable)
                (shortBinaryNumeralTerm width)
                (shortBinaryNumeralTerm start)
                (‘1’ : ValuationTerm) ⋏
              (“!!(shortBinaryNumeralTerm innerStart) <
                  !!(shortBinaryNumeralTerm tokenCount)” ⋏
                (“!!(shortBinaryNumeralTerm finish) =
                    !!(shortBinaryNumeralTerm innerStart) + 1” ⋏
                  compactFixedWidthEntryAtValuationFormula
                    (shortBinaryNumeralTerm tokenTable)
                    (shortBinaryNumeralTerm width)
                    (shortBinaryNumeralTerm innerStart)
                    (‘0’ : ValuationTerm))))))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (boundedWitnessGuardCertificate innerStart tokenCount hinner.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLtCertificate start tokenCount hinner.2.1.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (successorEqualityCertificate start innerStart hinner.2.1.2.1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            zeroValuation
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm start)
            (‘1’ : ValuationTerm) (by
              simpa [termValue_shortBinaryNumeralTerm,
                termValue_arithmeticOne,
                FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                using hinner.2.1.2.2))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (closedLtCertificate innerStart tokenCount hinner.2.2.1)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (successorEqualityCertificate innerStart finish
                hinner.2.2.2.1)
              (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                zeroValuation
                (shortBinaryNumeralTerm tokenTable)
                (shortBinaryNumeralTerm width)
                (shortBinaryNumeralTerm innerStart)
                (‘0’ : ValuationTerm) (by
                  simpa [termValue_shortBinaryNumeralTerm,
                    termValue_arithmeticZero,
                    FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                    using hinner.2.2.2.2)))))))

theorem compactBinaryNatFailedStatusSlice_deterministicWitness
    (tokenTable width tokenCount start finish : Nat)
    (hgraph : CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish) :
    start + 1 ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 (start + 1) ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount (start + 1) 0 finish := by
  rcases hgraph with ⟨candidate, hbound, hfirst, hsecond⟩
  have hcandidate : candidate = start + 1 := hfirst.2.1
  subst candidate
  exact ⟨hbound, hfirst, hsecond⟩

noncomputable def compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount start finish : Nat)
    (hgraph : CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish) :
    HybridCertificate
      (compactBinaryNatFailedStatusSliceClosedFormula
        tokenTable width tokenCount start finish) := by
  let innerStart := start + 1
  have hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 0 finish := by
    simpa only [innerStart] using
      compactBinaryNatFailedStatusSlice_deterministicWitness
        tokenTable width tokenCount start finish hgraph
  let post :=
    compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate
      tokenTable width tokenCount start finish innerStart hinner
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactBinaryNatFailedStatusSliceWitnessBody_substitution_alignment
      tokenTable width tokenCount start finish innerStart).symm post
  let direct := CheckedHybridValuationBoundedFormulaCertificate.existsWitness
    (compactBinaryNatFailedStatusSliceWitnessBody
      tokenTable width tokenCount start finish)
    innerStart instantiated
  exact .cast
    (compactBinaryNatFailedStatusSliceClosedFormula_alignment
      tokenTable width tokenCount start finish).symm direct

def compactBinaryNatCompletedStatusPrefixClosedFormula
    (tokenTable width tokenCount start outputStart : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactBinaryNatCompletedStatusPrefixDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm outputStart]

def compactBinaryNatCompletedStatusPrefixWitnessBody
    (tokenTable width tokenCount start outputStart : Nat) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (“!!(Rew.bShift (shortBinaryNumeralTerm start)) <
        !!(Rew.bShift (shortBinaryNumeralTerm tokenCount))” ⋏
      (“#0 = !!(Rew.bShift (shortBinaryNumeralTerm start)) + 1” ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
            Rew.bShift (shortBinaryNumeralTerm width),
            Rew.bShift (shortBinaryNumeralTerm start),
            Rew.bShift (‘1’ : ValuationTerm)]) ⋏
          (“#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount))” ⋏
            (“!!(Rew.bShift (shortBinaryNumeralTerm outputStart)) =
                #0 + 1” ⋏
              ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
                ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
                  Rew.bShift (shortBinaryNumeralTerm width),
                  (#0 : ArithmeticSemiterm Nat 1),
                  Rew.bShift (‘1’ : ValuationTerm)]))))))

theorem compactBinaryNatCompletedStatusPrefixClosedFormula_alignment
    (tokenTable width tokenCount start outputStart : Nat) :
    compactBinaryNatCompletedStatusPrefixClosedFormula
        tokenTable width tokenCount start outputStart =
      ∃⁰ compactBinaryNatCompletedStatusPrefixWitnessBody
        tokenTable width tokenCount start outputStart := by
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
  unfold compactBinaryNatCompletedStatusPrefixWitnessBody
  unfold compactBinaryNatCompletedStatusPrefixDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactBinaryNatCompletedStatusPrefixWitnessBody_substitution_alignment
    (tokenTable width tokenCount start outputStart innerStart : Nat) :
    (compactBinaryNatCompletedStatusPrefixWitnessBody
      tokenTable width tokenCount start outputStart)/[
        shortBinaryNumeralTerm innerStart] =
      (“!!(shortBinaryNumeralTerm innerStart) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
        (“!!(shortBinaryNumeralTerm start) <
            !!(shortBinaryNumeralTerm tokenCount)” ⋏
          (“!!(shortBinaryNumeralTerm innerStart) =
              !!(shortBinaryNumeralTerm start) + 1” ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm tokenTable)
                (shortBinaryNumeralTerm width)
                (shortBinaryNumeralTerm start)
                (‘1’ : ValuationTerm) ⋏
              (“!!(shortBinaryNumeralTerm innerStart) <
                  !!(shortBinaryNumeralTerm tokenCount)” ⋏
                (“!!(shortBinaryNumeralTerm outputStart) =
                    !!(shortBinaryNumeralTerm innerStart) + 1” ⋏
                  compactFixedWidthEntryAtValuationFormula
                    (shortBinaryNumeralTerm tokenTable)
                    (shortBinaryNumeralTerm width)
                    (shortBinaryNumeralTerm innerStart)
                    (‘1’ : ValuationTerm))))))) := by
  unfold compactBinaryNatCompletedStatusPrefixWitnessBody
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app, Rew.subst_bvar]
  constructor
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def
    compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate
    (tokenTable width tokenCount start outputStart innerStart : Nat)
    (hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 1 outputStart) :
    HybridCertificate
      (“!!(shortBinaryNumeralTerm innerStart) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
        (“!!(shortBinaryNumeralTerm start) <
            !!(shortBinaryNumeralTerm tokenCount)” ⋏
          (“!!(shortBinaryNumeralTerm innerStart) =
              !!(shortBinaryNumeralTerm start) + 1” ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm tokenTable)
                (shortBinaryNumeralTerm width)
                (shortBinaryNumeralTerm start)
                (‘1’ : ValuationTerm) ⋏
              (“!!(shortBinaryNumeralTerm innerStart) <
                  !!(shortBinaryNumeralTerm tokenCount)” ⋏
                (“!!(shortBinaryNumeralTerm outputStart) =
                    !!(shortBinaryNumeralTerm innerStart) + 1” ⋏
                  compactFixedWidthEntryAtValuationFormula
                    (shortBinaryNumeralTerm tokenTable)
                    (shortBinaryNumeralTerm width)
                    (shortBinaryNumeralTerm innerStart)
                    (‘1’ : ValuationTerm))))))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (boundedWitnessGuardCertificate innerStart tokenCount hinner.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLtCertificate start tokenCount hinner.2.1.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (successorEqualityCertificate start innerStart hinner.2.1.2.1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            zeroValuation
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm start)
            (‘1’ : ValuationTerm) (by
              simpa [termValue_shortBinaryNumeralTerm,
                termValue_arithmeticOne,
                FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                using hinner.2.1.2.2))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (closedLtCertificate innerStart tokenCount hinner.2.2.1)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (successorEqualityCertificate innerStart outputStart
                hinner.2.2.2.1)
              (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                zeroValuation
                (shortBinaryNumeralTerm tokenTable)
                (shortBinaryNumeralTerm width)
                (shortBinaryNumeralTerm innerStart)
                (‘1’ : ValuationTerm) (by
                  simpa [termValue_shortBinaryNumeralTerm,
                    termValue_arithmeticOne,
                    FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                    using hinner.2.2.2.2)))))))

theorem compactBinaryNatCompletedStatusPrefix_deterministicWitness
    (tokenTable width tokenCount start outputStart : Nat)
    (hgraph : CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount start outputStart) :
    start + 1 ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 (start + 1) ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount (start + 1) 1 outputStart := by
  rcases hgraph with ⟨candidate, hbound, hfirst, hsecond⟩
  have hcandidate : candidate = start + 1 := hfirst.2.1
  subst candidate
  exact ⟨hbound, hfirst, hsecond⟩

noncomputable def compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount start outputStart : Nat)
    (hgraph : CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount start outputStart) :
    HybridCertificate
      (compactBinaryNatCompletedStatusPrefixClosedFormula
        tokenTable width tokenCount start outputStart) := by
  let innerStart := start + 1
  have hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 1 outputStart := by
    simpa only [innerStart] using
      compactBinaryNatCompletedStatusPrefix_deterministicWitness
        tokenTable width tokenCount start outputStart hgraph
  let post :=
    compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate
      tokenTable width tokenCount start outputStart innerStart hinner
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactBinaryNatCompletedStatusPrefixWitnessBody_substitution_alignment
      tokenTable width tokenCount start outputStart innerStart).symm post
  let direct := CheckedHybridValuationBoundedFormulaCertificate.existsWitness
    (compactBinaryNatCompletedStatusPrefixWitnessBody
      tokenTable width tokenCount start outputStart)
    innerStart instantiated
  exact .cast
    (compactBinaryNatCompletedStatusPrefixClosedFormula_alignment
      tokenTable width tokenCount start outputStart).symm direct

#print axioms compactBinaryNatRunningStatusSliceClosedFormula_alignment
#print axioms compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
#print axioms compactBinaryNatFailedStatusSliceClosedFormula_alignment
#print axioms compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
#print axioms compactBinaryNatCompletedStatusPrefixClosedFormula_alignment
#print axioms compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
