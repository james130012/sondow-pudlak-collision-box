import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula

/-!
# Installation of the formula-task formula into the syntax parser step

For a running syntax parser whose task stack begins with kind `1`, the
handwritten Delta-zero formula has a witness exactly when the real public
parser step produces the specified next state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaTaskInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula

theorem compactSyntaxParserStep_formulaTaskFormula_iff
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hstatus : current.2.2 = none)
    {tail : List CompactSyntaxTask}
    (htasks : current.2.1 = (1, binderArity, 0) :: tail) :
    (∃ witness,
        compactUnifiedParserSyntaxFormulaRowsDef.val.Evalb
          (compactUnifiedParserSyntaxFormulaTaskEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              binderArity witness)) ↔
      next = compactSyntaxParserStep current := by
  rw [exists_compactUnifiedParserSyntaxFormulaTaskFormula_iff hcurrent hnext]
  rcases current with ⟨tokens, tasks, status⟩
  simp only at hstatus htasks ⊢
  subst status
  subst tasks
  simp [CompactSyntaxParserFormulaTaskCase,
    compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep]

#print axioms compactSyntaxParserStep_formulaTaskFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxFormulaTaskInstallation
