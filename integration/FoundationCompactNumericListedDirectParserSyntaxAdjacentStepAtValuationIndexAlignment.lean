import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexCurrentAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexNextAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexStepAlignment

/-! # Exact aggregate alignment for an adjacent step at an open index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexAlignment

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexCurrentAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexNextAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexStepAlignment

theorem compactParserSyntaxAdjacentStepRowAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserSyntaxAdjacentStepRowAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount indexTerm row =
      compactParserSyntaxAdjacentStepRowAtValuationIndexExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm row := by
  unfold compactParserSyntaxAdjacentStepRowAtValuationIndexFormula
  rw [compactParserSyntaxAdjacentStepRowDef_emb_decomposition]
  change
    ((Rew.subst
      (compactParserSyntaxAdjacentStepAtValuationIndexTerms tokenTable width
        tokenCount stateBoundary stateCount indexTerm row)) ▹
          compactParserSyntaxAdjacentStepSourceCurrentFormula) ⋏
      (((Rew.subst
        (compactParserSyntaxAdjacentStepAtValuationIndexTerms tokenTable width
          tokenCount stateBoundary stateCount indexTerm row)) ▹
            compactParserSyntaxAdjacentStepSourceNextFormula) ⋏
        ((Rew.subst
          (compactParserSyntaxAdjacentStepAtValuationIndexTerms tokenTable width
            tokenCount stateBoundary stateCount indexTerm row)) ▹
              compactParserSyntaxAdjacentStepSourceStepFormula)) =
      compactParserSyntaxAdjacentStepRowAtValuationIndexExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm row
  rw [compactParserSyntaxAdjacentStepCurrentAtValuationIndex_alignment,
    compactParserSyntaxAdjacentStepNextAtValuationIndex_alignment,
    compactParserSyntaxAdjacentStepRelationAtValuationIndex_alignment]
  rfl

#print axioms
  compactParserSyntaxAdjacentStepRowAtValuationIndexFormula_alignment

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexAlignment
