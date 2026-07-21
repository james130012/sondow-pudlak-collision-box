import integration.FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the compact negation-formula tag graph

The two bounded `pair < 4` branches retain the literal arithmetic trees from
the source graph.  Each selected pair is installed directly as a bounded
existential witness, and every remaining leaf is an atomic certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate

open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

def compactNegationFormulaTagClosedFormula
    (tag mapped : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNegationFormulaTagGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tag, shortBinaryNumeralTerm mapped]

/-- The exact bounded witness matrix for the even tag branch. -/
def compactNegationFormulaTagEvenWitnessBody
    (tag mapped : Nat) : ArithmeticSemiformula Nat 1 :=
  “#0 < 4” ⋏
    (“!!(Rew.bShift (shortBinaryNumeralTerm tag)) = 2 * #0” ⋏
      “!!(Rew.bShift (shortBinaryNumeralTerm mapped)) =
        !!(Rew.bShift (shortBinaryNumeralTerm tag)) + 1”)

/-- The exact bounded witness matrix for the odd tag branch. -/
def compactNegationFormulaTagOddWitnessBody
    (tag mapped : Nat) : ArithmeticSemiformula Nat 1 :=
  “#0 < 4” ⋏
    (“!!(Rew.bShift (shortBinaryNumeralTerm tag)) = 2 * #0 + 1” ⋏
      “!!(Rew.bShift (shortBinaryNumeralTerm tag)) =
        !!(Rew.bShift (shortBinaryNumeralTerm mapped)) + 1”)

def compactNegationFormulaTagExplicitFormula
    (tag mapped : Nat) : ValuationFormula :=
  (“!!(shortBinaryNumeralTerm tag) < 8” ⋏
    ((∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped) ⋎
      (∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped))) ⋎
  (“8 ≤ !!(shortBinaryNumeralTerm tag)” ⋏
    “!!(shortBinaryNumeralTerm mapped) = !!(shortBinaryNumeralTerm tag)”)

theorem compactNegationFormulaTagClosedFormula_alignment
    (tag mapped : Nat) :
    compactNegationFormulaTagClosedFormula tag mapped =
      compactNegationFormulaTagExplicitFormula tag mapped := by
  unfold compactNegationFormulaTagClosedFormula
  unfold compactNegationFormulaTagExplicitFormula
  unfold compactNegationFormulaTagEvenWitnessBody
  unfold compactNegationFormulaTagOddWitnessBody
  unfold compactNegationFormulaTagGraphDef
  simp [Semiformula.bexsLT, Semiformula.bexs_eq,
    Rew.subst_bvar, Rew.q]

theorem compactNegationFormulaTagEvenWitnessBody_substitution_alignment
    (tag mapped pair : Nat) :
    (compactNegationFormulaTagEvenWitnessBody tag mapped)/[
        shortBinaryNumeralTerm pair] =
      (“!!(shortBinaryNumeralTerm pair) < 4” ⋏
        (“!!(shortBinaryNumeralTerm tag) =
            2 * !!(shortBinaryNumeralTerm pair)” ⋏
          “!!(shortBinaryNumeralTerm mapped) =
            !!(shortBinaryNumeralTerm tag) + 1”)) := by
  unfold compactNegationFormulaTagEvenWitnessBody
  simp [Rew.subst_bvar]

theorem compactNegationFormulaTagOddWitnessBody_substitution_alignment
    (tag mapped pair : Nat) :
    (compactNegationFormulaTagOddWitnessBody tag mapped)/[
        shortBinaryNumeralTerm pair] =
      (“!!(shortBinaryNumeralTerm pair) < 4” ⋏
        (“!!(shortBinaryNumeralTerm tag) =
            2 * !!(shortBinaryNumeralTerm pair) + 1” ⋏
          “!!(shortBinaryNumeralTerm tag) =
            !!(shortBinaryNumeralTerm mapped) + 1”)) := by
  unfold compactNegationFormulaTagOddWitnessBody
  simp [Rew.subst_bvar]

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_arithmeticFour (valuation : Nat -> Nat) :
    termValue valuation (‘4’ : ValuationTerm) = 4 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_arithmeticEight (valuation : Nat -> Nat) :
    termValue valuation (‘8’ : ValuationTerm) = 8 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

noncomputable def pairLtFourCertificate
    (pair : Nat) (hpair : pair < 4) :
    HybridCertificate “!!(shortBinaryNumeralTerm pair) < 4” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm pair, (‘4’ : ValuationTerm)] (by
      change termValue zeroValuation (shortBinaryNumeralTerm pair) <
        termValue zeroValuation (‘4’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticFour] using hpair)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

noncomputable def tagLtEightCertificate
    (tag : Nat) (htag : tag < 8) :
    HybridCertificate “!!(shortBinaryNumeralTerm tag) < 8” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm tag, (‘8’ : ValuationTerm)] (by
      change termValue zeroValuation (shortBinaryNumeralTerm tag) <
        termValue zeroValuation (‘8’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticEight] using htag)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

noncomputable def evenTagEqualityCertificate
    (tag pair : Nat) (htag : tag = 2 * pair) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm tag) = 2 * !!(shortBinaryNumeralTerm pair)” := by
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm tag,
      (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)]
  change termValue zeroValuation (shortBinaryNumeralTerm tag) =
    termValue zeroValuation (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)
  simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticMul,
    termValue_arithmeticTwo] using htag

noncomputable def oddTagEqualityCertificate
    (tag pair : Nat) (htag : tag = 2 * pair + 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm tag) =
        2 * !!(shortBinaryNumeralTerm pair) + 1” := by
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm tag,
      (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ : ValuationTerm)]
  change termValue zeroValuation (shortBinaryNumeralTerm tag) =
    termValue zeroValuation
      (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ : ValuationTerm)
  simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
    termValue_arithmeticMul, termValue_arithmeticOne,
    termValue_arithmeticTwo] using htag

noncomputable def mappedSuccessorCertificate
    (tag mapped : Nat) (hmapped : mapped = tag + 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm mapped) =
        !!(shortBinaryNumeralTerm tag) + 1” := by
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm mapped,
      (‘!!(shortBinaryNumeralTerm tag) + 1’ : ValuationTerm)]
  change termValue zeroValuation (shortBinaryNumeralTerm mapped) =
    termValue zeroValuation
      (‘!!(shortBinaryNumeralTerm tag) + 1’ : ValuationTerm)
  simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
    termValue_arithmeticOne] using hmapped

noncomputable def tagMappedSuccessorCertificate
    (tag mapped : Nat) (htag : tag = mapped + 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm tag) =
        !!(shortBinaryNumeralTerm mapped) + 1” := by
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm tag,
      (‘!!(shortBinaryNumeralTerm mapped) + 1’ : ValuationTerm)]
  change termValue zeroValuation (shortBinaryNumeralTerm tag) =
    termValue zeroValuation
      (‘!!(shortBinaryNumeralTerm mapped) + 1’ : ValuationTerm)
  simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
    termValue_arithmeticOne] using htag

noncomputable def eightLeTagCertificate
    (tag : Nat) (htag : 8 ≤ tag) :
    HybridCertificate “8 ≤ !!(shortBinaryNumeralTerm tag)” := by
  if heq : 8 = tag then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] (by
        change termValue zeroValuation (‘8’ : ValuationTerm) =
          termValue zeroValuation (shortBinaryNumeralTerm tag)
        simpa [termValue_shortBinaryNumeralTerm,
          termValue_arithmeticEight] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : 8 < tag := Nat.lt_of_le_of_ne htag heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] (by
        change termValue zeroValuation (‘8’ : ValuationTerm) <
          termValue zeroValuation (shortBinaryNumeralTerm tag)
        simpa [termValue_shortBinaryNumeralTerm,
          termValue_arithmeticEight] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

noncomputable def mappedTagEqualityCertificate
    (tag mapped : Nat) (hmapped : mapped = tag) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm mapped) = !!(shortBinaryNumeralTerm tag)” := by
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm mapped, shortBinaryNumeralTerm tag]
  change termValue zeroValuation (shortBinaryNumeralTerm mapped) =
    termValue zeroValuation (shortBinaryNumeralTerm tag)
  simpa [termValue_shortBinaryNumeralTerm] using hmapped

noncomputable def compactNegationFormulaTagEvenWitnessCertificate
    (tag mapped pair : Nat)
    (hpair : pair < 4)
    (htag : tag = 2 * pair)
    (hmapped : mapped = tag + 1) :
    HybridCertificate
      (∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped) := by
  refine .existsWitness (compactNegationFormulaTagEvenWitnessBody tag mapped)
    pair ?_
  let body := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (pairLtFourCertificate pair hpair)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (evenTagEqualityCertificate tag pair htag)
      (mappedSuccessorCertificate tag mapped hmapped))
  exact .cast
    (compactNegationFormulaTagEvenWitnessBody_substitution_alignment
      tag mapped pair).symm body

noncomputable def compactNegationFormulaTagOddWitnessCertificate
    (tag mapped pair : Nat)
    (hpair : pair < 4)
    (htag : tag = 2 * pair + 1)
    (hmapped : tag = mapped + 1) :
    HybridCertificate
      (∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped) := by
  refine .existsWitness (compactNegationFormulaTagOddWitnessBody tag mapped)
    pair ?_
  let body := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (pairLtFourCertificate pair hpair)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (oddTagEqualityCertificate tag pair htag)
      (tagMappedSuccessorCertificate tag mapped hmapped))
  exact .cast
    (compactNegationFormulaTagOddWitnessBody_substitution_alignment
      tag mapped pair).symm body

inductive CompactNegationFormulaTagCheckedBranchData
    (tag mapped : Nat) : Type
  | even
      (hsmall : tag < 8)
      (pair : Nat)
      (hpair : pair < 4)
      (htag : tag = 2 * pair)
      (hmapped : mapped = tag + 1)
  | odd
      (hsmall : tag < 8)
      (pair : Nat)
      (hpair : pair < 4)
      (htag : tag = 2 * pair + 1)
      (hmapped : tag = mapped + 1)
  | large
      (hlarge : 8 ≤ tag)
      (hmapped : mapped = tag)

theorem compactNegationFormulaTagCheckedBranchData_nonempty
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    Nonempty (CompactNegationFormulaTagCheckedBranchData tag mapped) := by
  rcases hgraph with ⟨hsmall, heven | hodd⟩ | ⟨hlarge, hmapped⟩
  · rcases heven with ⟨pair, hpair, htag, hmapped⟩
    exact ⟨.even hsmall pair hpair htag hmapped⟩
  · rcases hodd with ⟨pair, hpair, htag, hmapped⟩
    exact ⟨.odd hsmall pair hpair htag hmapped⟩
  · exact ⟨.large hlarge hmapped⟩

noncomputable def compactNegationFormulaTagCheckedBranchDataOfGraph
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    CompactNegationFormulaTagCheckedBranchData tag mapped :=
  Classical.choice
    (compactNegationFormulaTagCheckedBranchData_nonempty tag mapped hgraph)

noncomputable def compactNegationFormulaTagExplicitHybridCertificateFromData
    (tag mapped : Nat)
    (data : CompactNegationFormulaTagCheckedBranchData tag mapped) :
    HybridCertificate
      (compactNegationFormulaTagExplicitFormula tag mapped) := by
  cases data with
  | even hsmall pair hpair htag hmapped =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (tagLtEightCertificate tag hsmall)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (compactNegationFormulaTagEvenWitnessCertificate
              tag mapped pair hpair htag hmapped)))
  | odd hsmall pair hpair htag hmapped =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (tagLtEightCertificate tag hsmall)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (compactNegationFormulaTagOddWitnessCertificate
              tag mapped pair hpair htag hmapped)))
  | large hlarge hmapped =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (eightLeTagCertificate tag hlarge)
          (mappedTagEqualityCertificate tag mapped hmapped))

noncomputable def compactNegationFormulaTagExplicitHybridCertificateOfGraph
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
  HybridCertificate (compactNegationFormulaTagClosedFormula tag mapped) :=
  .cast (compactNegationFormulaTagClosedFormula_alignment tag mapped).symm
    (compactNegationFormulaTagExplicitHybridCertificateFromData tag mapped
      (compactNegationFormulaTagCheckedBranchDataOfGraph tag mapped hgraph))

noncomputable def compileCompactNegationFormulaTagExplicitHybridContext
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    CertifiedPAContextProof
      (valuationContext
        (compactNegationFormulaTagClosedFormula tag mapped).freeVariables
        zeroValuation)
      (compactNegationFormulaTagClosedFormula tag mapped) :=
  (compactNegationFormulaTagExplicitHybridCertificateOfGraph
    tag mapped hgraph).compile

noncomputable def compactNegationFormulaTagExplicitStructuralResource
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactNegationFormulaTagExplicitHybridCertificateOfGraph
      tag mapped hgraph)

theorem compileCompactNegationFormulaTagExplicitHybridContext_payloadLength_le
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    (compileCompactNegationFormulaTagExplicitHybridContext
      tag mapped hgraph).payloadLength ≤
      compactNegationFormulaTagExplicitStructuralResource tag mapped hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactNegationFormulaTagExplicitHybridCertificateOfGraph
      tag mapped hgraph)

#print axioms compactNegationFormulaTagClosedFormula_alignment
#print axioms compactNegationFormulaTagCheckedBranchData_nonempty
#print axioms compactNegationFormulaTagExplicitHybridCertificateFromData
#print axioms compactNegationFormulaTagExplicitHybridCertificateOfGraph
#print axioms
  compileCompactNegationFormulaTagExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
