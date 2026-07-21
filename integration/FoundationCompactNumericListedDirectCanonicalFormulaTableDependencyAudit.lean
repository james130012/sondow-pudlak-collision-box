import integration.FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplitExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceTableExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierInitialParseBranchInversion
import Lean

/-!
# Dependency audit for the explicit canonical formula table

This probe follows project declarations transitively from the public explicit
endpoints.  It fails elaboration if the route reaches a Sigma-zero truth
selector or the retained legacy outer-witness endpoint.
-/

open Lean Elab Term Meta Std

namespace FoundationCompactNumericListedDirectCanonicalFormulaTableDependencyAudit

private def isProjectDeclaration (name : Name) : Bool :=
  (name.toString.splitOn ".").any fun component =>
    component.startsWith "Foundation"

private def isForbiddenDeclaration (name : Name) : Bool :=
  let text := name.toString
  text.endsWith ".ofSigmaZeroTruth" ||
    text.endsWith ".certificate_nonempty_of_sigmaZero_truth" ||
    text.endsWith ".compactCanonicalFormulaTableOuterWitnessCertificate"

private partial def auditDependencyClosure
    (pending : List Name) (seen : HashSet Name) :
    TermElabM (HashSet Name) := do
  match pending with
  | [] => pure seen
  | name :: rest =>
      if seen.contains name then
        auditDependencyClosure rest seen
      else if isForbiddenDeclaration name then
        throwError m!"explicit formula-table route reaches forbidden declaration {name}"
      else
        let seen := seen.insert name
        let dependencies <- try
          let info <- getConstInfo name
          pure <| match info.value? with
            | some body => body.getUsedConstants.toList
            | none => []
        catch _ => pure []
        let projectDependencies :=
          dependencies.filter isProjectDeclaration
        auditDependencyClosure (projectDependencies ++ rest) seen

private def auditExplicitFormulaTableRoute : TermElabM Unit := do
  let roots := [
    `FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate.compactCanonicalFormulaTableExplicitCertificate,
    `FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate.compactCanonicalFormulaTableExplicitCertificateAtCode,
    `FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition.boundedWitnessInputTableauExplicitCertificate,
    `FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition.boundedWitnessFormulaTableauExplicitCertificate,
    `FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowExplicitHybridCertificate.compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificate,
    `FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate.compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate,
    `FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate.compileCompactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridContext_payloadLength_le,
    `FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplitExplicitHybridCertificate.boundedWitnessInputSplitExplicitHybridCertificate,
    `FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplitExplicitHybridCertificate.compileBoundedWitnessInputSplitExplicitHybridContext_payloadLength_le,
    `FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate.compactNumericVerifierAcceptedTraceFinalExplicitHybridCertificate,
    `FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate.compileCompactNumericVerifierAcceptedTraceFinalExplicitHybridContext_payloadLength_le,
    `FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition.compactNumericVerifierAcceptedTraceTableClosedFormula_eq_decomposed,
    `FoundationCompactNumericListedDirectVerifierAcceptedTraceTableExplicitHybridCertificate.compactNumericVerifierAcceptedTraceTableExplicitHybridCertificateOfComponents,
    `FoundationCompactNumericListedDirectVerifierInitialParseBranchInversion.compactNumericVerifierInitialParseBranchInversion,
    `FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate.compileCompactCanonicalFormulaTableExplicit,
    `FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate.compileCompactCanonicalFormulaTableExplicit_publicVerifier_eq_true,
    `FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate.compileCompactCanonicalFormulaTableExplicit_payloadLength_le_structure
  ]
  let closure <- auditDependencyClosure roots HashSet.emptyWithCapacity
  logInfo m!"explicit formula-table dependency audit passed ({closure.size} project declarations)"

#eval auditExplicitFormulaTableRoute

end FoundationCompactNumericListedDirectCanonicalFormulaTableDependencyAudit
