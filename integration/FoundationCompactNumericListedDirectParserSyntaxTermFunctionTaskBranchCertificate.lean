import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate

/-!
# Named function-task branch certificate

Naming the fixed `(2, binderArity, functionArity)` ConsRows certificate keeps
the large dependent expression out of downstream theorem signatures.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

noncomputable def syntaxTermFunctionTaskCertificate
    (tokenTable width tokenCount tailBoundary tailCount targetBoundary
      targetCount binderArity functionArity : Nat)
    (htasks : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount targetBoundary targetCount 2 binderArity
      functionArity) :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount tailBoundary tailCount targetBoundary
    targetCount 2 binderArity functionArity (fixedNumeralTerm 2)
    (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm functionArity)
    (fun valuation => by simp)
    (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
    (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) htasks

#print axioms syntaxTermFunctionTaskCertificate

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchCertificate
