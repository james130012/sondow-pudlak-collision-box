import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailCertificate

/-! # Clean running-and-tail parts certificate for the syntax-formula parser -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate

noncomputable def compactUnifiedParserSyntaxFormulaCleanRunningCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
      (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
        tokenCount current.tasksFinish current.finish) :=
  compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable
    width tokenCount current.tasksFinish current.finish hgraph.1

noncomputable def compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactUnifiedParserSyntaxFormulaCleanRunningCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph)
    (compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph)

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
