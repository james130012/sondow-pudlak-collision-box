import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsSubstitutionAlignment
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsFreeAlignment
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowEntryExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowCoreRevalueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowBranchExplicitHybridCertificate

/-!
# Explicit hybrid certificate for verifier task-list rows

This cached second stage installs the fourteen concrete row witnesses and
assembles the public certificate from the source-formula alignment.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitWitnessExsClosureBuilder

private noncomputable def
    compactNumericVerifierTaskListRowsExponentialCertificate
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    HybridCertificate zeroValuation
      (compactNumericVerifierTaskListRowsExponentialClosedFormula
        tableWidth valueBound) := by
  change HybridCertificate zeroValuation
    (exponentialAtValuationFormula
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))
  exact .exponential zeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

private noncomputable def
    compactNumericVerifierTaskListRowsExplicitFormulaHybridCertificateOfGraph
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat)
    (hgraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount taskBoundary taskCount
        tableWidth valueBound) :
    HybridCertificate zeroValuation
      (compactNumericVerifierTaskListRowsExplicitFormula
        tokenTable width tokenCount taskBoundary taskCount
          tableWidth valueBound) := by
  let exponential :=
    compactNumericVerifierTaskListRowsExponentialCertificate
      tableWidth valueBound hgraph.1
  let body := compactNumericVerifierTaskListRowsUniversalBody
    tokenTable width tokenCount taskBoundary valueBound
  let branches := buildExplicitHybridUniversalBranches taskCount
    (fun rowIndex hrowIndex =>
      compactNumericVerifierTaskListRowBranchExplicitHybridCertificate
        tokenTable width tokenCount taskBoundary valueBound rowIndex
          (hgraph.2 rowIndex hrowIndex))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm taskCount) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  let universal : HybridCertificate zeroValuation
      (body.ballLT (shortBinaryNumeralTerm taskCount)) := .cast (by
        change (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm taskCount)) body) =
            body.ballLT (shortBinaryNumeralTerm taskCount)
        rw [termBoundedUniversal_eq_ball]
        rfl) direct
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    exponential universal

/-- Public arbitrary-task-count constructor directly from the semantic graph. -/
noncomputable def
    compactNumericVerifierTaskListRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat)
    (hgraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount taskBoundary taskCount
        tableWidth valueBound) :
    HybridCertificate zeroValuation
      (compactNumericVerifierTaskListRowsClosedFormula
        tokenTable width tokenCount taskBoundary taskCount
          tableWidth valueBound) := by
  exact .cast
    (compactNumericVerifierTaskListRowsClosedFormula_alignment
      tokenTable width tokenCount taskBoundary taskCount
        tableWidth valueBound).symm
    (compactNumericVerifierTaskListRowsExplicitFormulaHybridCertificateOfGraph
      tokenTable width tokenCount taskBoundary taskCount
        tableWidth valueBound hgraph)

#print axioms compactNumericVerifierTaskListRowsClosedFormula_alignment
#print axioms compactNumericVerifierTaskListRowsSourceUniversalBody_alignment
#print axioms compactNumericVerifierTaskListRowsUniversalBody_free_alignment
#print axioms
  compactNumericVerifierTaskListRowsBranchTerminal_substitution_alignment
#print axioms
  compactNumericVerifierTaskListRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
