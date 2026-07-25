import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

/-! # Shared exact terminal certificate for Repeat task-row lookups -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

theorem termValue_successorIndexTerm_repeatAtRows
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    termValue valuation (successorIndexTerm term) =
      termValue valuation term + 1 := by
  unfold successorIndexTerm
  rw [show
    (‘!!term + 1’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![term, (‘1’ : ValuationTerm)] by
        simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
          Rew.func, Matrix.fun_eq_vec_two]]
  calc
    termValue valuation
        (Semiterm.func Language.Add.add ![term, (‘1’ : ValuationTerm)]) =
      termValue valuation term +
        termValue valuation (‘1’ : ValuationTerm) :=
          termValue_add valuation ![term, (‘1’ : ValuationTerm)]
    _ = termValue valuation term + 1 := by
      rw [show termValue valuation (‘1’ : ValuationTerm) = 1 by
        exact termValue_one valuation ![]]

theorem successorIndexTerm_freeVariables_eq_empty_repeatAtRows
    (term : ValuationTerm) (hterm : term.freeVariables = ∅) :
    (successorIndexTerm term).freeVariables = ∅ := by
  unfold successorIndexTerm
  rw [FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds.arithmeticAddTerm_freeVariables_eq_union,
    hterm]
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

noncomputable def repeatAtRowsTerminalCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index kind binderArity
      repeatCount : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexValue : termValue atRowsZeroValuation indexTerm = index)
    (hkindValue : forall valuation, termValue valuation kindTerm = kind)
    (hbinderValue :
      forall valuation, termValue valuation binderArityTerm = binderArity)
    (hrepeatValue :
      forall valuation, termValue valuation repeatCountTerm = repeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount) :
    let left := Classical.choose hgraph.2
    let leftData := Classical.choose_spec hgraph.2
    let right := Classical.choose leftData.2
    let values : Fin 2 -> Nat := ![right, left]
    let body :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
        width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
          repeatCountTerm
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (body ⇜ fun coordinate =>
        shortBinaryNumeralTerm (values coordinate)) := by
  dsimp only
  let left := Classical.choose hgraph.2
  have leftData := Classical.choose_spec hgraph.2
  let right := Classical.choose leftData.2
  have rightData := Classical.choose_spec leftData.2
  let values : Fin 2 -> Nat := ![right, left]
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm left) (by
          simpa only [termValue_shortBinaryNumeralTerm, hindexValue] using
            rightData.2.1))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (successorIndexTerm indexTerm)
          (shortBinaryNumeralTerm right) (by
            simpa only [termValue_shortBinaryNumeralTerm, hindexValue,
              termValue_successorIndexTerm_repeatAtRows] using
              rightData.2.2.1))
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount left right kind binderArity repeatCount
          kindTerm binderArityTerm repeatCountTerm hkindValue hbinderValue
          hrepeatValue rightData.2.2.2))
  apply CheckedHybridValuationBoundedFormulaCertificate.cast _ parts
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [hvalueTerms]
  exact
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
      tokenTable width tokenCount boundaryTable left right indexTerm kindTerm
      binderArityTerm repeatCountTerm).symm

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate
