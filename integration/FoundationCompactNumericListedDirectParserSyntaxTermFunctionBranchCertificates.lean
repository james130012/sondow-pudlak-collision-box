import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchCertificate

/-!
# Named branch certificates for the function syntax-term transition

The running, drop-three, function-task, and conjunction certificates are
named once so downstream bounds do not repeatedly elaborate their dependent
types.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionBranchCertificates

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchCertificate

noncomputable def syntaxTermFunctionRunningCertificate
    (tokenTable width tokenCount tasksFinish finish : Nat)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      tasksFinish finish) :=
  compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
    tokenTable width tokenCount tasksFinish finish hrunning

noncomputable def syntaxTermFunctionTokensCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount : Nat)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3) :=
  compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    targetCount 3 htokens

noncomputable def syntaxTermFunctionTailCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount tailBoundary tailCount tasksBoundary tasksCount binderArity
      functionArity : Nat)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (htasks : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount tasksBoundary tasksCount 2 binderArity
      functionArity) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (syntaxTermFunctionTokensCertificate tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount htokens)
    (syntaxTermFunctionTaskCertificate tokenTable width tokenCount tailBoundary
      tailCount tasksBoundary tasksCount binderArity functionArity htasks)

noncomputable def syntaxTermFunctionPartsCertificate
    (tokenTable width tokenCount tasksFinish finish sourceBoundary sourceCount
      targetBoundary targetCount tailBoundary tailCount tasksBoundary
      tasksCount binderArity functionArity : Nat)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      tasksFinish finish)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (htasks : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount tasksBoundary tasksCount 2 binderArity
      functionArity) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (syntaxTermFunctionRunningCertificate tokenTable width tokenCount
      tasksFinish finish hrunning)
    (syntaxTermFunctionTailCertificate tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount tailBoundary
      tailCount tasksBoundary tasksCount binderArity functionArity htokens
      htasks)

#print axioms syntaxTermFunctionRunningCertificate
#print axioms syntaxTermFunctionTokensCertificate
#print axioms syntaxTermFunctionTailCertificate
#print axioms syntaxTermFunctionPartsCertificate

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionBranchCertificates
