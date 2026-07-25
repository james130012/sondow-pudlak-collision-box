import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fixed formula and assembly envelope for the function syntax-term transition

This module caches the closed 23-coordinate formula and the three-branch
payload envelope before the graph certificate is assembled.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds

def syntaxTermFunctionAssemblySyntaxEnvelope
    (_tokenCount _numericBound bitBound : Nat) : Nat :=
  syntaxTermFunctionClosedFormulaCodePolynomial bitBound

def syntaxTermFunctionFullyFixedPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (syntaxTermFunctionAssemblySyntaxEnvelope tokenCount numericBound
      bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    (dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)

def syntaxTermFunctionPartsTransparentEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity numericBound bitBound :
      Nat) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount 3
  let tasksFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
  let tailEnvelope := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation
    tokensFormula tasksFormula
    (dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound bitBound)
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation
    runningFormula (tokensFormula ⋏ tasksFormula)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    tailEnvelope

theorem
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) :
    (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next tailBoundary tailCount binderArity
      functionArity).freeVariables = ∅ :=
  syntaxTermFunctionClosedFormula_freeVariables_eq_empty tokenTable width
    tokenCount current next tailBoundary tailCount binderArity functionArity

#print axioms
  compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
