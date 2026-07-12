import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFormula

/-!
# Installation of the repeated-term formula into the syntax parser step

For a running syntax parser whose task stack begins with kind `2`, the
handwritten Delta-zero formula has a witness exactly when the real public
parser step produces the specified next state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula

theorem compactSyntaxParserStep_repeatFormula_iff
    {tokenTable width tokenCount binderArity repeatCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hstatus : current.2.2 = none)
    {tail : List CompactSyntaxTask}
    (htasks : current.2.1 = (2, binderArity, repeatCount) :: tail) :
    (∃ witness,
        compactUnifiedParserSyntaxRepeatRowsDef.val.Evalb
          (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf
            tokenTable width tokenCount currentCoordinates nextCoordinates
              binderArity repeatCount witness)) ↔
      next = compactSyntaxParserStep current := by
  rw [exists_compactUnifiedParserSyntaxRepeatFormula_iff hcurrent hnext]
  rcases current with ⟨tokens, tasks, status⟩
  simp only at hstatus htasks ⊢
  subst status
  subst tasks
  simp [CompactSyntaxParserRepeatTaskCase,
    compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep]

#print axioms compactSyntaxParserStep_repeatFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxRepeatInstallation
