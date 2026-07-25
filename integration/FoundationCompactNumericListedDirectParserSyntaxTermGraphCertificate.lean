import integration.FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds

/-! # Fixed certificate constructor for the complete syntax-term graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

noncomputable def syntaxTermFullyFixedGraphBranchData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    CompactSyntaxTermCheckedBranchData tokenTable width tokenCount current next
      binderArity witness :=
  compactSyntaxTermCheckedBranchDataOfGraph tokenTable width tokenCount current
    next binderArity witness hgraph

noncomputable def syntaxTermFullyFixedGraphRunningCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    TermHybridCertificate
      (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
        tokenCount current.tasksFinish current.finish) :=
  compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current.tasksFinish current.finish hgraph.1

theorem syntaxTermFullyFixedGraphRunningCertificate_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    syntaxTermFullyFixedGraphRunningCertificate tokenTable width tokenCount
        current next binderArity witness hgraph =
      compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish
        hgraph.1 :=
  rfl

theorem syntaxTermFullyFixedGraphRunningCertificate_structuralPayload_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphRunningCertificate tokenTable width
          tokenCount current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tasksFinish current.finish
          hgraph.1) :=
  congrArg hybridFormulaStructuralPayloadBound
    (syntaxTermFullyFixedGraphRunningCertificate_eq tokenTable width tokenCount
      current next binderArity witness hgraph)

theorem fixedNumeralTerm_zero_eq_shortBinaryNumeralTerm_zero :
    fixedNumeralTerm 0 = shortBinaryNumeralTerm 0 := by
  simp [fixedNumeralTerm, shortBinaryNumeralTerm,
    FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
    FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
    LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]

noncomputable def syntaxTermFullyFixedGraphUnconsCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    TermHybridCertificate
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
        tokenTable width tokenCount current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
        (fixedNumeralTerm 0)) := by
  let canonical :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 0
      binderArity 0 (shortBinaryNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm 0)
      (termValue_shortBinaryNumeralTerm · 0)
      (termValue_shortBinaryNumeralTerm · binderArity)
      (termValue_shortBinaryNumeralTerm · 0) hgraph.2.1
  have hformula :
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize
          (shortBinaryNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm 0) =
        compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0) := by
    rw [fixedNumeralTerm_zero_eq_shortBinaryNumeralTerm_zero]
  exact CheckedHybridValuationBoundedFormulaCertificate.cast hformula canonical

theorem syntaxTermFullyFixedGraphUnconsCertificate_structuralPayload_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphUnconsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize 0
          binderArity 0 (shortBinaryNumeralTerm 0)
          (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm 0)
          (termValue_shortBinaryNumeralTerm · 0)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · 0) hgraph.2.1) := by
  unfold syntaxTermFullyFixedGraphUnconsCertificate
  rfl

noncomputable def syntaxTermFullyFixedGraphBranchCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) :=
  syntaxTermFullyFixedBranchCertificateFromData tokenTable width tokenCount
    current next binderArity witness
    (syntaxTermFullyFixedGraphBranchData tokenTable width tokenCount current
      next binderArity witness hgraph)

theorem syntaxTermFullyFixedGraphBranchCertificate_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    syntaxTermFullyFixedGraphBranchCertificate tokenTable width tokenCount
        current next binderArity witness hgraph =
      syntaxTermFullyFixedBranchCertificateFromData tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermFullyFixedGraphBranchData tokenTable width tokenCount current
          next binderArity witness hgraph) :=
  rfl

theorem syntaxTermFullyFixedGraphBranchCertificate_structuralPayload_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphBranchCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedBranchCertificateFromData tokenTable width
          tokenCount current next binderArity witness
          (syntaxTermFullyFixedGraphBranchData tokenTable width tokenCount
            current next binderArity witness hgraph)) :=
  congrArg hybridFormulaStructuralPayloadBound
    (syntaxTermFullyFixedGraphBranchCertificate_eq tokenTable width tokenCount
      current next binderArity witness hgraph)

noncomputable def syntaxTermFullyFixedGraphTailCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    TermHybridCertificate
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0) ⋏
        compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
          tokenCount current next binderArity witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (syntaxTermFullyFixedGraphUnconsCertificate tokenTable width tokenCount
      current next binderArity witness hgraph)
    (syntaxTermFullyFixedGraphBranchCertificate tokenTable width tokenCount
      current next binderArity witness hgraph)

theorem syntaxTermFullyFixedGraphTailCertificate_eq_conjunction
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount current
        next binderArity witness hgraph =
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (syntaxTermFullyFixedGraphUnconsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph)
        (syntaxTermFullyFixedGraphBranchCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) :=
  rfl

theorem syntaxTermFullyFixedGraphTailCertificate_structuralPayload_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (syntaxTermFullyFixedGraphUnconsCertificate tokenTable width
            tokenCount current next binderArity witness hgraph)
          (syntaxTermFullyFixedGraphBranchCertificate tokenTable width
            tokenCount current next binderArity witness hgraph)) :=
  congrArg hybridFormulaStructuralPayloadBound
    (syntaxTermFullyFixedGraphTailCertificate_eq_conjunction tokenTable width
      tokenCount current next binderArity witness hgraph)

noncomputable def syntaxTermFullyFixedGraphPartsCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermExplicitFormula tokenTable width tokenCount
        current next binderArity witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (syntaxTermFullyFixedGraphRunningCertificate tokenTable width tokenCount
      current next binderArity witness hgraph)
    (syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount
      current next binderArity witness hgraph)

theorem syntaxTermFullyFixedGraphPartsCertificate_eq_conjunction
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
        current next binderArity witness hgraph =
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (syntaxTermFullyFixedGraphRunningCertificate tokenTable width tokenCount
          current next binderArity witness hgraph)
        (syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) :=
  rfl

theorem syntaxTermFullyFixedGraphPartsCertificate_structuralPayload_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (syntaxTermFullyFixedGraphRunningCertificate tokenTable width
            tokenCount current next binderArity witness hgraph)
          (syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount
            current next binderArity witness hgraph)) :=
  congrArg hybridFormulaStructuralPayloadBound
    (syntaxTermFullyFixedGraphPartsCertificate_eq_conjunction tokenTable width
      tokenCount current next binderArity witness hgraph)

noncomputable def syntaxTermFullyFixedGraphCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current next binderArity witness) := by
  exact .cast
    (compactUnifiedParserSyntaxTermClosedFormula_alignment tokenTable width
      tokenCount current next binderArity witness).symm
    (syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
      current next binderArity witness hgraph)

theorem syntaxTermFullyFixedGraphCertificate_eq_cast_parts
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount current
        next binderArity witness hgraph =
      CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxTermClosedFormula_alignment tokenTable width
          tokenCount current next binderArity witness).symm
        (syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) := by
  rfl

theorem syntaxTermFullyFixedGraphCertificate_structuralPayload_eq_parts
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) := by
  unfold syntaxTermFullyFixedGraphCertificate
  rfl

end FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
