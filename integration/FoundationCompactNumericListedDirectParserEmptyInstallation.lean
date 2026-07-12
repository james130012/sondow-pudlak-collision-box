import integration.FoundationCompactNumericListedDirectParserEmptyFormula
import integration.FoundationCompactNumericListedDirectParserStepCases

/-!
# Installation of the empty-task formula into all three parser steps

For fixed current and next parser-state rows, a running state with an empty
task stack satisfies the handwritten Delta-zero graph exactly when the public
syntax, proof, or certificate parser step completes with the remaining tokens.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserEmptyInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserEmptyRows
open FoundationCompactNumericListedDirectParserEmptyFormula

theorem compactSyntaxParserStep_emptyFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hstatus : current.2.2 = none)
    (htasks : current.2.1 = []) :
    (∃ witness,
        compactUnifiedParserEmptyGraphRowsDef.val.Evalb
          (compactUnifiedParserEmptyFormulaEnvironmentOf
            tokenTable width tokenCount
              currentCoordinates nextCoordinates witness)) ↔
      next = compactSyntaxParserStep current := by
  simp only [compactUnifiedParserEmptyGraphRowsDef_environmentOf_iff]
  rw [exists_compactUnifiedParserEmptyGraphRows_iff hcurrent hnext]
  simp [CompactUnifiedParserStepEmptyCase,
    hstatus, htasks, compactSyntaxParserStep, compactSyntaxRunningStep]

theorem compactProofParserStep_emptyFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactProofParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hstatus : current.2.2 = none)
    (htasks : current.2.1 = []) :
    (∃ witness,
        compactUnifiedParserEmptyGraphRowsDef.val.Evalb
          (compactUnifiedParserEmptyFormulaEnvironmentOf
            tokenTable width tokenCount
              currentCoordinates nextCoordinates witness)) ↔
      next = compactProofParserStep current := by
  simp only [compactUnifiedParserEmptyGraphRowsDef_environmentOf_iff]
  rw [exists_compactUnifiedParserEmptyGraphRows_iff hcurrent hnext]
  simp [CompactUnifiedParserStepEmptyCase,
    hstatus, htasks, compactProofParserStep, compactProofParserRunningStep]

theorem compactCertificateParserStep_emptyFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactCertificateParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hstatus : current.2.2 = none)
    (htasks : current.2.1 = []) :
    (∃ witness,
        compactUnifiedParserEmptyGraphRowsDef.val.Evalb
          (compactUnifiedParserEmptyFormulaEnvironmentOf
            tokenTable width tokenCount
              currentCoordinates nextCoordinates witness)) ↔
      next = compactCertificateParserStep current := by
  simp only [compactUnifiedParserEmptyGraphRowsDef_environmentOf_iff]
  rw [exists_compactUnifiedParserEmptyGraphRows_iff hcurrent hnext]
  simp [CompactUnifiedParserStepEmptyCase,
    hstatus, htasks,
    compactCertificateParserStep, compactCertificateParserRunningStep]

#print axioms compactSyntaxParserStep_emptyFormula_iff
#print axioms compactProofParserStep_emptyFormula_iff
#print axioms compactCertificateParserStep_emptyFormula_iff

end FoundationCompactNumericListedDirectParserEmptyInstallation
