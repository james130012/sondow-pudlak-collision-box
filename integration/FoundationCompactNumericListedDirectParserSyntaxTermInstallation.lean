import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula

/-!
# Installation of the term-task formula into the syntax parser step

For a running syntax parser whose task stack begins with kind `0`, the
handwritten Delta-zero formula has a witness exactly when the real public
parser step produces the specified next state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTermInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula

theorem compactSyntaxParserStep_termFormula_iff
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
    (htasks : current.2.1 = (0, binderArity, 0) :: tail) :
    (∃ witness,
        compactUnifiedParserSyntaxTermRowsDef.val.Evalb
          (compactUnifiedParserSyntaxTermFormulaEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              binderArity witness)) ↔
      next = compactSyntaxParserStep current := by
  rw [exists_compactUnifiedParserSyntaxTermFormula_iff hcurrent hnext]
  rcases current with ⟨tokens, tasks, status⟩
  simp only at hstatus htasks ⊢
  subst status
  subst tasks
  simp [CompactSyntaxParserTermTaskCase,
    compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep]

#print axioms compactSyntaxParserStep_termFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxTermInstallation
