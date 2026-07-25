import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsCertificate

/-! # Clean complete graph certificate for the syntax-formula parser -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate

private abbrev cleanFormulaZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation

noncomputable def
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    CheckedHybridValuationBoundedFormulaCertificate cleanFormulaZeroValuation
      (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current next binderArity witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactUnifiedParserSyntaxFormulaClosedFormula_alignment tokenTable width
      tokenCount current next binderArity witness).symm
    (compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph)

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
