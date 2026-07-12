import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidFormula

/-!
# Installation of the invalid-kind formula into the syntax parser step

For a running syntax parser whose task head has a kind outside `0`, `1`, and
`2`, the bounded formula has a witness exactly when the public parser step
enters its specified failed state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxInvalidInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula

theorem compactSyntaxParserStep_invalidTaskFormula_iff
    {tokenTable width tokenCount kind binderArity repeatCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hstatus : current.2.2 = none)
    {tail : List CompactSyntaxTask}
    (htasks : current.2.1 = (kind, binderArity, repeatCount) :: tail)
    (hkindZero : kind ≠ 0)
    (hkindOne : kind ≠ 1)
    (hkindTwo : kind ≠ 2) :
    (∃ witness,
        compactUnifiedParserSyntaxInvalidRowsDef.val.Evalb
          (compactUnifiedParserSyntaxInvalidFormulaEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              witness)) ↔
      next = compactSyntaxParserStep current := by
  rw [exists_compactUnifiedParserSyntaxInvalidFormula_iff hcurrent hnext]
  rcases current with ⟨tokens, tasks, status⟩
  simp only at hstatus htasks ⊢
  subst status
  subst tasks
  simp [CompactSyntaxParserInvalidTaskCase,
    compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep, hkindZero, hkindOne, hkindTwo]

#print axioms compactSyntaxParserStep_invalidTaskFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxInvalidInstallation
