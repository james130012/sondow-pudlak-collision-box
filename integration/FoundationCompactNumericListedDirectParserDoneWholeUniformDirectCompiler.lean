import integration.FoundationCompactNumericListedDirectParserDoneStatusUniformDirectCompiler

/-! # Uniform direct compiler for the complete parser Done formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserDoneWholeUniformDirectCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneStatusUniformDirectCompiler

private abbrev doneDirectZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

noncomputable def compileCompactUnifiedParserDoneUniformDirectExplicitContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.outputCount <= numericBound)
    (hsourceBoundarySize :
      Nat.size witness.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserDoneExplicitFormula tokenTable width tokenCount
          current next witness).freeVariables doneDirectZeroValuation)
      (compactUnifiedParserDoneExplicitFormula tokenTable width tokenCount
        current next witness) := by
  rcases hgraph with ⟨htokens, htasks, hstatus⟩
  let tokens :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  let tasks :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      next.tasksBoundary next.tasksCount htasks
  let status :=
    compileCompactUnifiedParserDoneStatusUniformDirect tokenTable width
      tokenCount current next witness numericBound bitBound hstatus
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize
  exact compileDirectConjunction tokens.compile
    (compileDirectConjunction tasks.compile status)

end FoundationCompactNumericListedDirectParserDoneWholeUniformDirectCompiler
