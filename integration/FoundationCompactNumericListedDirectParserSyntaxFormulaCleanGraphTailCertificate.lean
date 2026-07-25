import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataFullyFixedBounds

/-! # Clean tail certificate for the syntax-formula parser graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCleanCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

noncomputable def compactUnifiedParserSyntaxFormulaCleanUnconsCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
        tokenTable width tokenCount current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
        (fixedNumeralTerm 0)) :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current.tasksBoundary current.tasksCount
    witness.tailBoundary witness.tailCount witness.tailBoundarySize 1
    binderArity 0 (fixedNumeralTerm 1)
    (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
    (fun valuation => by simp)
    (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
    (fun valuation => by simp) hgraph.2.1

noncomputable def compactUnifiedParserSyntaxFormulaCleanBranchCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) :=
  compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData
    tokenTable width tokenCount current next binderArity witness
    (compactSyntaxFormulaCheckedBranchDataOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph)

noncomputable def compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactUnifiedParserSyntaxFormulaCleanUnconsCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph)
    (compactUnifiedParserSyntaxFormulaCleanBranchCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph)

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
