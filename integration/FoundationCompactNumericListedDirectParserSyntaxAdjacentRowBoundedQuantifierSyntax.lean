import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitution

/-! # Closed twenty-seven-witness formula alignment -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntax

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitution

private theorem
    compactParserSyntaxAdjacentRowBoundedSourceRawBody_alignment
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) :
    Rew.subst
        (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
          tokenCount stateBoundary stateCount index valueBound) ▹
      compactParserSyntaxAdjacentRowBoundedSourceRawBody =
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27
      (compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount index valueBound) := by
  unfold compactParserSyntaxAdjacentRowBoundedSourceRawBody
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactParserSyntaxAdjacentRowBoundedSourceRawTerminal_rewriting]
  have hbound :
      Rew.subst
          (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
            tokenCount stateBoundary stateCount index valueBound)
          (#6 : ArithmeticSemiterm Nat 7) =
        shortBinaryNumeralTerm valueBound := by
    simp [Rew.subst_bvar,
      compactParserSyntaxAdjacentRowBoundedSourceTerms]
  rw [hbound]
  rfl

theorem compactParserSyntaxAdjacentRowBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) :
    compactParserSyntaxAdjacentRowBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27
        (compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width
          tokenCount stateBoundary stateCount index valueBound) := by
  unfold compactParserSyntaxAdjacentRowBoundedClosedFormula
  rw [compactParserSyntaxAdjacentRowBoundedDef_emb_eq_sourceRawBody]
  exact compactParserSyntaxAdjacentRowBoundedSourceRawBody_alignment tokenTable
    width tokenCount stateBoundary stateCount index valueBound

#print axioms compactParserSyntaxAdjacentRowBoundedClosedFormula_alignment

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntax
