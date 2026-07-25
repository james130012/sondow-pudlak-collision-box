import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierRowSubstitution
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierStatusSubstitution

/-! # Combined public-parameter substitution for the adjacent-row terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitution

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierRowSubstitution
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierStatusSubstitution

theorem compactParserSyntaxAdjacentRowBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
          tokenCount stateBoundary stateCount index valueBound) 27 ▹
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal =
    compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount index valueBound := by
  change sourceSubstitutionQpow
      (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
        tokenCount stateBoundary stateCount index valueBound) 27 ▹
      (compactParserSyntaxAdjacentRowSourceRowFormula ⋏
        (compactParserSyntaxAdjacentRowSourceCurrentStatusFormula ⋏
          compactParserSyntaxAdjacentRowSourceNextStatusFormula)) =
    compactParserSyntaxAdjacentRowRawRowFormula tokenTable width tokenCount
        stateBoundary stateCount index ⋏
      (compactParserSyntaxAdjacentRowRawCurrentStatusFormula tokenTable width
          tokenCount valueBound ⋏
        compactParserSyntaxAdjacentRowRawNextStatusFormula tokenTable width
          tokenCount valueBound)
  change
    (sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
          tokenCount stateBoundary stateCount index valueBound) 27 ▹
        compactParserSyntaxAdjacentRowSourceRowFormula) ⋏
      ((sourceSubstitutionQpow
          (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
            tokenCount stateBoundary stateCount index valueBound) 27 ▹
          compactParserSyntaxAdjacentRowSourceCurrentStatusFormula) ⋏
        (sourceSubstitutionQpow
          (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
            tokenCount stateBoundary stateCount index valueBound) 27 ▹
          compactParserSyntaxAdjacentRowSourceNextStatusFormula)) =
      compactParserSyntaxAdjacentRowRawRowFormula tokenTable width tokenCount
          stateBoundary stateCount index ⋏
        (compactParserSyntaxAdjacentRowRawCurrentStatusFormula tokenTable width
            tokenCount valueBound ⋏
          compactParserSyntaxAdjacentRowRawNextStatusFormula tokenTable width
            tokenCount valueBound)
  rw [compactParserSyntaxAdjacentRowSourceRowFormula_rewriting]
  rw [compactParserSyntaxAdjacentRowSourceCurrentStatusFormula_rewriting]
  rw [compactParserSyntaxAdjacentRowSourceNextStatusFormula_rewriting]

#print axioms
  compactParserSyntaxAdjacentRowBoundedSourceRawTerminal_rewriting

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitution
