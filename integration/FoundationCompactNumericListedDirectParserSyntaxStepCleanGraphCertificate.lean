import integration.FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate

/-!
# Clean graph certificate for one syntax-parser step

This is the actual six-way syntax-step formula.  Its formula branch uses the
clean formula-parser certificate; the other five already checked branches are
reused without changing their formulas.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate

private abbrev cleanStepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate cleanStepZeroValuation formula

noncomputable def compactUnifiedParserSyntaxStepCleanHybridCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (data : CompactUnifiedParserSyntaxStepCheckedBranchData tokenTable width
      tokenCount current next witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness) := by
  unfold compactUnifiedParserSyntaxStepExplicitFormula
  cases data with
  | done hgraph =>
      exact .disjunctionLeft
        (compactUnifiedParserDoneExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness.done hgraph)
  | empty hgraph =>
      exact .disjunctionRight (.disjunctionLeft
        (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness.empty hgraph))
  | repeatBranch hgraph =>
      exact .disjunctionRight (.disjunctionRight (.disjunctionLeft
        (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.slot0 witness.slot1
          witness.repeat hgraph)))
  | term hgraph =>
      exact .disjunctionRight (.disjunctionRight (.disjunctionRight
        (.disjunctionLeft
          (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.slot0 witness.term
            hgraph))))
  | formula hgraph =>
      exact .disjunctionRight (.disjunctionRight (.disjunctionRight
        (.disjunctionRight (.disjunctionLeft
          (compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.slot0
            witness.formula hgraph)))))
  | invalid hgraph =>
      exact .disjunctionRight (.disjunctionRight (.disjunctionRight
        (.disjunctionRight (.disjunctionRight
          (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.invalid hgraph)))))

noncomputable def compactUnifiedParserSyntaxStepCleanHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount
      current next witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
        current next witness) :=
  .cast
    (compactUnifiedParserSyntaxStepClosedFormula_alignment tokenTable width
      tokenCount current next witness).symm
    (compactUnifiedParserSyntaxStepCleanHybridCertificateFromData tokenTable
      width tokenCount current next witness
      (compactUnifiedParserSyntaxStepCheckedBranchDataOfGraph tokenTable width
        tokenCount current next witness hgraph))

#print axioms compactUnifiedParserSyntaxStepCleanHybridCertificateFromData
#print axioms compactUnifiedParserSyntaxStepCleanHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
