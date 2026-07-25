import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

/-!
# Fixed syntax facts for the relation-body formula tree

The original right-associated relation formula is named node by node.  Closed
and code bounds for every node are extracted from the already proved bound for
the complete relation body.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodyTreeFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate

def relationBodyFailureFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
    tokenCount current next witness.tailBoundary witness.tailCount

def relationBodyFunctionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
    width tokenCount current next witness.tailBoundary witness.tailCount
    binderArity witness.relationArity

def relationBodyAtArityFormula
    (tokenTable width tokenCount : Nat)
    (current : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
    tokenCount current.tokensBoundary current.tokensCount
    witness.relationArity (fixedNumeralTerm 1)

def relationBodyAtCodeFormula
    (tokenTable width tokenCount : Nat)
    (current : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
    tokenCount current.tokensBoundary current.tokensCount witness.relationCode
    (fixedNumeralTerm 2)

def relationBodyValidFormula
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactAdditiveArithmeticRelCodeValidClosedFormula witness.relationArity
    witness.relationCode

def relationBodyInvalidFormula
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactAdditiveArithmeticRelCodeInvalidClosedFormula witness.relationArity
    witness.relationCode

def relationBodyLongGuardFormula
    (current : CompactUnifiedParserStateRowCoordinates) : ValuationFormula :=
  nativeShortLeFormula 3 current.tokensCount

def relationBodyShortBranchFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  shortNativeLeFormula current.tokensCount 2 ⋏
    relationBodyFailureFormula tokenTable width tokenCount current next witness

def relationBodyValidPairFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  relationBodyValidFormula witness ⋏
    relationBodyFunctionFormula tokenTable width tokenCount current next
      binderArity witness

def relationBodyInvalidPairFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  relationBodyInvalidFormula witness ⋏
    relationBodyFailureFormula tokenTable width tokenCount current next witness

def relationBodyChoiceFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  relationBodyValidPairFormula tokenTable width tokenCount current next
      binderArity witness ⋎
    relationBodyInvalidPairFormula tokenTable width tokenCount current next
      witness

def relationBodyCodeTailFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  relationBodyAtCodeFormula tokenTable width tokenCount current witness ⋏
    relationBodyChoiceFormula tokenTable width tokenCount current next
      binderArity witness

def relationBodyArityTailFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  relationBodyAtArityFormula tokenTable width tokenCount current witness ⋏
    relationBodyCodeTailFormula tokenTable width tokenCount current next
      binderArity witness

def relationBodyLongBranchFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  relationBodyLongGuardFormula current ⋏
    relationBodyArityTailFormula tokenTable width tokenCount current next
      binderArity witness

def relationBodyTreeFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  relationBodyShortBranchFormula tokenTable width tokenCount current next
      witness ⋎
    relationBodyLongBranchFormula tokenTable width tokenCount current next
      binderArity witness

theorem relationBodyTreeFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    relationBodyTreeFormula tokenTable width tokenCount current next
        binderArity witness =
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
        width tokenCount current next binderArity witness := by
  rfl

private theorem binaryFormulaCode_and_left_le
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_and_right_le
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_left_le
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem closed_children_and
    {left right : ValuationFormula}
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ ∧ right.freeVariables = ∅ := by
  simpa only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty] using hclosed

private theorem closed_children_or
    {left right : ValuationFormula}
    (hclosed : (left ⋎ right).freeVariables = ∅) :
    left.freeVariables = ∅ ∧ right.freeVariables = ∅ := by
  simpa only [LO.FirstOrder.Semiformula.freeVariables_or,
    Finset.union_eq_empty] using hclosed

structure RelationBodyTreeFixedFacts
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (syntaxResource : Nat) : Prop where
  shortBranchClosed :
    (relationBodyShortBranchFormula tokenTable width tokenCount current next
      witness).freeVariables = ∅
  longBranchClosed :
    (relationBodyLongBranchFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅
  longGuardClosed : (relationBodyLongGuardFormula current).freeVariables = ∅
  atArityClosed :
    (relationBodyAtArityFormula tokenTable width tokenCount current
      witness).freeVariables = ∅
  atCodeClosed :
    (relationBodyAtCodeFormula tokenTable width tokenCount current
      witness).freeVariables = ∅
  validClosed : (relationBodyValidFormula witness).freeVariables = ∅
  functionClosed :
    (relationBodyFunctionFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅
  invalidClosed : (relationBodyInvalidFormula witness).freeVariables = ∅
  failureClosed :
    (relationBodyFailureFormula tokenTable width tokenCount current next
      witness).freeVariables = ∅
  validPairClosed :
    (relationBodyValidPairFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅
  invalidPairClosed :
    (relationBodyInvalidPairFormula tokenTable width tokenCount current next
      witness).freeVariables = ∅
  choiceClosed :
    (relationBodyChoiceFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅
  codeTailClosed :
    (relationBodyCodeTailFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅
  arityTailClosed :
    (relationBodyArityTailFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅
  bodyClosed :
    (relationBodyTreeFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅
  shortBranchCode :
    (binaryFormulaCode
      (relationBodyShortBranchFormula tokenTable width tokenCount current next
        witness)).length <= syntaxResource
  longBranchCode :
    (binaryFormulaCode
      (relationBodyLongBranchFormula tokenTable width tokenCount current next
        binderArity witness)).length <= syntaxResource
  longGuardCode :
    (binaryFormulaCode (relationBodyLongGuardFormula current)).length <=
      syntaxResource
  atArityCode :
    (binaryFormulaCode
      (relationBodyAtArityFormula tokenTable width tokenCount current
        witness)).length <= syntaxResource
  atCodeCode :
    (binaryFormulaCode
      (relationBodyAtCodeFormula tokenTable width tokenCount current
        witness)).length <= syntaxResource
  validCode :
    (binaryFormulaCode (relationBodyValidFormula witness)).length <=
      syntaxResource
  functionCode :
    (binaryFormulaCode
      (relationBodyFunctionFormula tokenTable width tokenCount current next
        binderArity witness)).length <= syntaxResource
  invalidCode :
    (binaryFormulaCode (relationBodyInvalidFormula witness)).length <=
      syntaxResource
  failureCode :
    (binaryFormulaCode
      (relationBodyFailureFormula tokenTable width tokenCount current next
        witness)).length <= syntaxResource
  validPairCode :
    (binaryFormulaCode
      (relationBodyValidPairFormula tokenTable width tokenCount current next
        binderArity witness)).length <= syntaxResource
  invalidPairCode :
    (binaryFormulaCode
      (relationBodyInvalidPairFormula tokenTable width tokenCount current next
        witness)).length <= syntaxResource
  choiceCode :
    (binaryFormulaCode
      (relationBodyChoiceFormula tokenTable width tokenCount current next
        binderArity witness)).length <= syntaxResource
  codeTailCode :
    (binaryFormulaCode
      (relationBodyCodeTailFormula tokenTable width tokenCount current next
        binderArity witness)).length <= syntaxResource
  arityTailCode :
    (binaryFormulaCode
      (relationBodyArityTailFormula tokenTable width tokenCount current next
        binderArity witness)).length <= syntaxResource
  bodyCode :
    (binaryFormulaCode
      (relationBodyTreeFormula tokenTable width tokenCount current next
        binderArity witness)).length <= syntaxResource

theorem relationBodyTreeFixedFacts
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htailCountSize : Nat.size witness.tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound) :
    RelationBodyTreeFixedFacts tokenTable width tokenCount current next
      binderArity witness (syntaxFormulaRelationBodyCodePolynomial bitBound) := by
  let shortBranch :=
    relationBodyShortBranchFormula tokenTable width tokenCount current next
      witness
  let longBranch :=
    relationBodyLongBranchFormula tokenTable width tokenCount current next
      binderArity witness
  let longGuard := relationBodyLongGuardFormula current
  let atArity :=
    relationBodyAtArityFormula tokenTable width tokenCount current witness
  let atCode :=
    relationBodyAtCodeFormula tokenTable width tokenCount current witness
  let valid := relationBodyValidFormula witness
  let function :=
    relationBodyFunctionFormula tokenTable width tokenCount current next
      binderArity witness
  let invalid := relationBodyInvalidFormula witness
  let failure :=
    relationBodyFailureFormula tokenTable width tokenCount current next witness
  let validPair :=
    relationBodyValidPairFormula tokenTable width tokenCount current next
      binderArity witness
  let invalidPair :=
    relationBodyInvalidPairFormula tokenTable width tokenCount current next
      witness
  let choice :=
    relationBodyChoiceFormula tokenTable width tokenCount current next
      binderArity witness
  let codeTail :=
    relationBodyCodeTailFormula tokenTable width tokenCount current next
      binderArity witness
  let arityTail :=
    relationBodyArityTailFormula tokenTable width tokenCount current next
      binderArity witness
  let body :=
    relationBodyTreeFormula tokenTable width tokenCount current next
      binderArity witness
  have hbodyClosed : body.freeVariables = ∅ := by
    dsimp only [body]
    rw [relationBodyTreeFormula_alignment]
    exact
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount current next binderArity witness
  have hbodyCode :
      (binaryFormulaCode body).length <=
        syntaxFormulaRelationBodyCodePolynomial bitBound := by
    dsimp only [body]
    rw [relationBodyTreeFormula_alignment]
    exact
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_code_length_le_fixed
        tokenTable width tokenCount current next binderArity witness bitBound
        htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
        htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
        hrelationCodeSize
  have hbodyShape : body = shortBranch ⋎ longBranch := rfl
  have hlongShape : longBranch = longGuard ⋏ arityTail := rfl
  have harityShape : arityTail = atArity ⋏ codeTail := rfl
  have hcodeShape : codeTail = atCode ⋏ choice := rfl
  have hchoiceShape : choice = validPair ⋎ invalidPair := rfl
  have hvalidShape : validPair = valid ⋏ function := rfl
  have hinvalidShape : invalidPair = invalid ⋏ failure := rfl
  have hbodyChildren := closed_children_or (hbodyShape ▸ hbodyClosed)
  have hlongChildren := closed_children_and
    (hlongShape ▸ hbodyChildren.2)
  have harityChildren := closed_children_and
    (harityShape ▸ hlongChildren.2)
  have hcodeChildren := closed_children_and
    (hcodeShape ▸ harityChildren.2)
  have hchoiceChildren := closed_children_or
    (hchoiceShape ▸ hcodeChildren.2)
  have hvalidChildren := closed_children_and
    (hvalidShape ▸ hchoiceChildren.1)
  have hinvalidChildren := closed_children_and
    (hinvalidShape ▸ hchoiceChildren.2)
  have hshortCode :=
    (binaryFormulaCode_or_left_le shortBranch longBranch).trans
      (hbodyShape ▸ hbodyCode)
  have hlongCode :=
    (binaryFormulaCode_or_right_le shortBranch longBranch).trans
      (hbodyShape ▸ hbodyCode)
  have hlongGuardCode :=
    (binaryFormulaCode_and_left_le longGuard arityTail).trans
      (hlongShape ▸ hlongCode)
  have harityTailCode :=
    (binaryFormulaCode_and_right_le longGuard arityTail).trans
      (hlongShape ▸ hlongCode)
  have hatArityCode :=
    (binaryFormulaCode_and_left_le atArity codeTail).trans
      (harityShape ▸ harityTailCode)
  have hcodeTailCode :=
    (binaryFormulaCode_and_right_le atArity codeTail).trans
      (harityShape ▸ harityTailCode)
  have hatCodeCode :=
    (binaryFormulaCode_and_left_le atCode choice).trans
      (hcodeShape ▸ hcodeTailCode)
  have hchoiceCode :=
    (binaryFormulaCode_and_right_le atCode choice).trans
      (hcodeShape ▸ hcodeTailCode)
  have hvalidPairCode :=
    (binaryFormulaCode_or_left_le validPair invalidPair).trans
      (hchoiceShape ▸ hchoiceCode)
  have hinvalidPairCode :=
    (binaryFormulaCode_or_right_le validPair invalidPair).trans
      (hchoiceShape ▸ hchoiceCode)
  have hvalidCode :=
    (binaryFormulaCode_and_left_le valid function).trans
      (hvalidShape ▸ hvalidPairCode)
  have hfunctionCode :=
    (binaryFormulaCode_and_right_le valid function).trans
      (hvalidShape ▸ hvalidPairCode)
  have hinvalidCode :=
    (binaryFormulaCode_and_left_le invalid failure).trans
      (hinvalidShape ▸ hinvalidPairCode)
  have hfailureCode :=
    (binaryFormulaCode_and_right_le invalid failure).trans
      (hinvalidShape ▸ hinvalidPairCode)
  exact {
    shortBranchClosed := hbodyChildren.1
    longBranchClosed := hbodyChildren.2
    longGuardClosed := hlongChildren.1
    atArityClosed := harityChildren.1
    atCodeClosed := hcodeChildren.1
    validClosed := hvalidChildren.1
    functionClosed := hvalidChildren.2
    invalidClosed := hinvalidChildren.1
    failureClosed := hinvalidChildren.2
    validPairClosed := hchoiceChildren.1
    invalidPairClosed := hchoiceChildren.2
    choiceClosed := hcodeChildren.2
    codeTailClosed := harityChildren.2
    arityTailClosed := hlongChildren.2
    bodyClosed := hbodyClosed
    shortBranchCode := hshortCode
    longBranchCode := hlongCode
    longGuardCode := hlongGuardCode
    atArityCode := hatArityCode
    atCodeCode := hatCodeCode
    validCode := hvalidCode
    functionCode := hfunctionCode
    invalidCode := hinvalidCode
    failureCode := hfailureCode
    validPairCode := hvalidPairCode
    invalidPairCode := hinvalidPairCode
    choiceCode := hchoiceCode
    codeTailCode := hcodeTailCode
    arityTailCode := harityTailCode
    bodyCode := hbodyCode
  }

#print axioms relationBodyTreeFormula_alignment
#print axioms relationBodyTreeFixedFacts

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodyTreeFixedBounds
