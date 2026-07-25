import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate

/-! # Complete exact Repeat task-row certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

noncomputable def repeatAtRowsFullCertificateOfGraph
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
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
        repeatCountTerm) := by
  let guard :=
    strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
      simpa only [hindexValue, termValue_shortBinaryNumeralTerm] using hgraph.1)
  let installed :=
    repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount indexTerm kindTerm
      binderArityTerm repeatCountTerm hindexValue hkindValue hbinderValue
      hrepeatValue hgraph
  let witnessFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
      width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
      repeatCountTerm
  let witness :
      CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
        witnessFormula :=
    .cast (by
      unfold witnessFormula
        compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
      rw [explicitBoundedWitnessFormula_two_eq]) installed
  let raw :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction guard witness
  apply CheckedHybridValuationBoundedFormulaCertificate.cast _ raw
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment]
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula
  rfl

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate
