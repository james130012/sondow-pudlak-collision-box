import integration.FoundationCompactNumericListedDirectSequentFormulaTraceFormula
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

/-! # Direct closed syntax for the bounded sequent-formula trace -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

def compactSequentFormulaTraceBoundedDirectClosedFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactSequentFormulaTraceBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm suffixBoundary,
      shortBinaryNumeralTerm suffixCount,
      shortBinaryNumeralTerm valueBoundary,
      shortBinaryNumeralTerm valueCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactSequentFormulaTraceBoundedDirectExplicitFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1” ⋏
    (compactAdditiveNatListListRowsClosedFormula tokenTable width tokenCount
        suffixBoundary suffixCount ⋏
      (compactAdditiveNatListListRowsClosedFormula tokenTable width tokenCount
          valueBoundary valueCount ⋏
        compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          valueCount tableWidth valueBound))

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

theorem compactSequentFormulaTraceBoundedDirectClosedFormula_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat) :
    compactSequentFormulaTraceBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        tableWidth valueBound =
      compactSequentFormulaTraceBoundedDirectExplicitFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        tableWidth valueBound := by
  unfold compactSequentFormulaTraceBoundedDirectClosedFormula
    compactSequentFormulaTraceBoundedDirectExplicitFormula
    compactSequentFormulaTraceBoundedGraphDef
    compactAdditiveNatListListRowsClosedFormula
    compactSequentFormulaStepRowsBoundedDirectClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

#print axioms compactSequentFormulaTraceBoundedDirectClosedFormula_alignment

end FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax
