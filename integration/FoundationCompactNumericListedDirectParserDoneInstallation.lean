import integration.FoundationCompactNumericListedDirectParserDoneFormula
import integration.FoundationCompactNumericListedDirectParserStepCases

/-!
# Installation of the finished-branch formula into all three parser steps

For two fixed parser-state rows whose current status is already finished, an
explicit witness satisfying the handwritten Delta-zero done formula exists if
and only if the public syntax, proof, or certificate parser step produces the
given next state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserDoneInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneRows
open FoundationCompactNumericListedDirectParserDoneFormula

theorem compactSyntaxParserStep_doneFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hfinished : current.2.2.isSome = true) :
    (∃ witness,
        compactUnifiedParserDoneGraphRowsDef.val.Evalb
          (compactUnifiedParserDoneFormulaEnvironmentOf
            tokenTable width tokenCount
              currentCoordinates nextCoordinates witness)) ↔
      next = compactSyntaxParserStep current := by
  simp only [compactUnifiedParserDoneGraphRowsDef_environmentOf_iff]
  rw [exists_compactUnifiedParserDoneGraphRows_iff hcurrent hnext]
  rw [compactUnifiedParserStepDoneCase_iff_outer_done]
  simp [hfinished, compactSyntaxParserStep]

theorem compactProofParserStep_doneFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactProofParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hfinished : current.2.2.isSome = true) :
    (∃ witness,
        compactUnifiedParserDoneGraphRowsDef.val.Evalb
          (compactUnifiedParserDoneFormulaEnvironmentOf
            tokenTable width tokenCount
              currentCoordinates nextCoordinates witness)) ↔
      next = compactProofParserStep current := by
  simp only [compactUnifiedParserDoneGraphRowsDef_environmentOf_iff]
  rw [exists_compactUnifiedParserDoneGraphRows_iff hcurrent hnext]
  rw [compactUnifiedParserStepDoneCase_iff_outer_done]
  simp [hfinished, compactProofParserStep]

theorem compactCertificateParserStep_doneFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactCertificateParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hfinished : current.2.2.isSome = true) :
    (∃ witness,
        compactUnifiedParserDoneGraphRowsDef.val.Evalb
          (compactUnifiedParserDoneFormulaEnvironmentOf
            tokenTable width tokenCount
              currentCoordinates nextCoordinates witness)) ↔
      next = compactCertificateParserStep current := by
  simp only [compactUnifiedParserDoneGraphRowsDef_environmentOf_iff]
  rw [exists_compactUnifiedParserDoneGraphRows_iff hcurrent hnext]
  rw [compactUnifiedParserStepDoneCase_iff_outer_done]
  simp [hfinished, compactCertificateParserStep]

#print axioms compactSyntaxParserStep_doneFormula_iff
#print axioms compactProofParserStep_doneFormula_iff
#print axioms compactCertificateParserStep_doneFormula_iff

end FoundationCompactNumericListedDirectParserDoneInstallation
