import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicFiniteUniversalBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds

/-!
# Public structural resources for the repeated parser task

The repeat branch is charged from its checked running-status, list, uncons,
same/drop/at-row, and native arithmetic certificates.  The zero and successor
alternatives are assembled with transparent connective envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

private abbrev binaryStatusZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

private abbrev natListZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation

private abbrev unconsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation

private abbrev dropZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem fixedNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

def compactUnifiedParserSyntaxRepeatNativeEqPayloadPolynomial
    (value expected : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial repeatZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]

theorem nativeEqCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (heq : value = expected) :
    hybridFormulaStructuralPayloadBound
        (nativeEqCertificate value expected heq) ≤
      compactUnifiedParserSyntaxRepeatNativeEqPayloadPolynomial value
        expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (fixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    repeatZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
    hleft hright
  change compilePositiveRelationPayloadResource repeatZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] ≤ _
  exact hpublic

def compactUnifiedParserSyntaxRepeatNativeSuccessorEqPayloadPolynomial
    (value predecessor : Nat) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm predecessor) + !!(fixedNumeralTerm 1)’
  compilePositiveRelationPayloadPolynomial repeatZeroValuation
    Language.Eq.eq ![shortBinaryNumeralTerm value, rightTerm]

theorem nativeSuccessorEqCertificate_structuralPayloadBound_le_public
    (value predecessor : Nat) (heq : value = predecessor + 1) :
    hybridFormulaStructuralPayloadBound
        (nativeSuccessorEqCertificate value predecessor heq) ≤
      compactUnifiedParserSyntaxRepeatNativeSuccessorEqPayloadPolynomial
        value predecessor := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm predecessor) + !!(fixedNumeralTerm 1)’
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : rightTerm.freeVariables ⊆ {0} := by
    rw [hrightClosed]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    repeatZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, rightTerm] hleft hright
  change compilePositiveRelationPayloadResource repeatZeroValuation
      Language.Eq.eq ![shortBinaryNumeralTerm value, rightTerm] ≤ _
  exact hpublic

noncomputable def compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (branchData : CompactSyntaxRepeatCheckedBranchData tokenTable width
      tokenCount next binderArity repeatCount witness) : Nat := by
  let currentFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let nextFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let unconsFormula :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      binderArity repeatCount (fixedNumeralTerm 2)
  let zeroEqFormula := nativeEqFormula repeatCount 0
  let sameFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount witness.tailBoundary witness.tailCount
    next.tasksBoundary next.tasksCount
  let zeroBranchFormula := zeroEqFormula ⋏ sameFormula
  let successorEqFormula := nativeSuccessorEqFormula repeatCount
    witness.decrementedCount
  let dropFormula := compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
    witness.tailBoundary witness.tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
  let positiveBranchFormula := successorEqFormula ⋏
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
  let branchFormula := zeroBranchFormula ⋎ positiveBranchFormula
  let currentResource :=
    compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount current.tasksFinish current.finish
  let nextResource :=
    compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish
  let tokensResource := compactAdditiveNatListSameRowsGraphPayloadEnvelope
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount htokens
  let unconsResource :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 2
      binderArity repeatCount (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm repeatCount) huncons
  let branchResource : Nat := by
    rcases branchData with ⟨hrepeatZero, hsame⟩ |
      ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
    ·
      let zeroPairResource := transparentHybridConjunctionPayloadEnvelope
        repeatZeroValuation zeroEqFormula sameFormula
        (compactUnifiedParserSyntaxRepeatNativeEqPayloadPolynomial repeatCount 0)
        (compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable
          width tokenCount witness.tailBoundary witness.tailCount
          next.tasksBoundary next.tasksCount hsame)
      exact transparentHybridDisjunctionLeftPayloadEnvelope
        repeatZeroValuation zeroBranchFormula positiveBranchFormula
        zeroPairResource
    ·
      let taskPairResource := transparentHybridConjunctionPayloadEnvelope
        atRowsZeroValuation taskZeroFormula taskOneFormula
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          0 0 binderArity 0 (fixedNumeralTerm 0) (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
          htaskZero)
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          1 2 binderArity witness.decrementedCount (fixedNumeralTerm 1)
          (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm witness.decrementedCount) htaskOne)
      let dropTailResource := transparentHybridConjunctionPayloadEnvelope
        dropZeroValuation dropFormula
        (taskZeroFormula ⋏ taskOneFormula)
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          witness.tailBoundary witness.tailCount 2 hdrop)
        taskPairResource
      let positiveResource := transparentHybridConjunctionPayloadEnvelope
        repeatZeroValuation successorEqFormula
        (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
        (compactUnifiedParserSyntaxRepeatNativeSuccessorEqPayloadPolynomial
          repeatCount witness.decrementedCount)
        dropTailResource
      exact transparentHybridDisjunctionRightPayloadEnvelope
        repeatZeroValuation zeroBranchFormula positiveBranchFormula
        positiveResource
  let unconsBranchResource := transparentHybridConjunctionPayloadEnvelope
    unconsZeroValuation unconsFormula branchFormula unconsResource
    branchResource
  let tokensTailResource := transparentHybridConjunctionPayloadEnvelope
    natListZeroValuation tokensFormula (unconsFormula ⋏ branchFormula)
    tokensResource unconsBranchResource
  let nextTailResource := transparentHybridConjunctionPayloadEnvelope
    binaryStatusZeroValuation nextFormula
    (tokensFormula ⋏ (unconsFormula ⋏ branchFormula)) nextResource
    tokensTailResource
  exact transparentHybridConjunctionPayloadEnvelope binaryStatusZeroValuation
    currentFormula
    (nextFormula ⋏ (tokensFormula ⋏ (unconsFormula ⋏ branchFormula)))
    currentResource nextTailResource

noncomputable def compactUnifiedParserSyntaxRepeatGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next binderArity repeatCount witness) : Nat :=
  compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope tokenTable width
    tokenCount current next binderArity repeatCount witness hgraph.1
    hgraph.2.1 hgraph.2.2.1 hgraph.2.2.2.1
    (compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
      next binderArity repeatCount witness hgraph.2.2.2.2)

def compactUnifiedParserSyntaxRepeatZeroBranchPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : Nat :=
  let zeroEqFormula := nativeEqFormula repeatCount 0
  let sameFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount witness.tailBoundary witness.tailCount
    next.tasksBoundary next.tasksCount
  let zeroBranchFormula := zeroEqFormula ⋏ sameFormula
  let successorEqFormula := nativeSuccessorEqFormula repeatCount
    witness.decrementedCount
  let dropFormula := compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
    witness.tailBoundary witness.tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
  let positiveBranchFormula := successorEqFormula ⋏
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
  let zeroPairResource := transparentHybridConjunctionPayloadEnvelope
    repeatZeroValuation zeroEqFormula sameFormula
    (compactUnifiedParserSyntaxRepeatNativeEqPayloadPolynomial repeatCount 0)
    (compactAdditiveSyntaxTaskListSameRowsPublicFinitePayloadEnvelope tokenTable
      width tokenCount witness.tailBoundary witness.tailCount
      next.tasksBoundary next.tasksCount)
  transparentHybridDisjunctionLeftPayloadEnvelope repeatZeroValuation
    zeroBranchFormula positiveBranchFormula zeroPairResource

def compactUnifiedParserSyntaxRepeatPositiveBranchPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : Nat :=
  let zeroEqFormula := nativeEqFormula repeatCount 0
  let sameFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount witness.tailBoundary witness.tailCount
    next.tasksBoundary next.tasksCount
  let zeroBranchFormula := zeroEqFormula ⋏ sameFormula
  let successorEqFormula := nativeSuccessorEqFormula repeatCount
    witness.decrementedCount
  let dropFormula := compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
    witness.tailBoundary witness.tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
  let positiveBranchFormula := successorEqFormula ⋏
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
  let taskPairResource := transparentHybridConjunctionPayloadEnvelope
    atRowsZeroValuation taskZeroFormula taskOneFormula
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 0
      binderArity 0 (fixedNumeralTerm 0) (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0))
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 2
      binderArity witness.decrementedCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount))
  let dropTailResource := transparentHybridConjunctionPayloadEnvelope
    dropZeroValuation dropFormula (taskZeroFormula ⋏ taskOneFormula)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFinitePayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      witness.tailBoundary witness.tailCount 2)
    taskPairResource
  let positiveResource := transparentHybridConjunctionPayloadEnvelope
    repeatZeroValuation successorEqFormula
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
    (compactUnifiedParserSyntaxRepeatNativeSuccessorEqPayloadPolynomial
      repeatCount witness.decrementedCount)
    dropTailResource
  transparentHybridDisjunctionRightPayloadEnvelope repeatZeroValuation
    zeroBranchFormula positiveBranchFormula positiveResource

noncomputable def compactUnifiedParserSyntaxRepeatZeroBranchGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount) : Nat :=
  let zeroEqFormula := nativeEqFormula repeatCount 0
  let sameFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount witness.tailBoundary witness.tailCount
    next.tasksBoundary next.tasksCount
  let zeroBranchFormula := zeroEqFormula ⋏ sameFormula
  let successorEqFormula := nativeSuccessorEqFormula repeatCount
    witness.decrementedCount
  let dropFormula := compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
    witness.tailBoundary witness.tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
  let positiveBranchFormula := successorEqFormula ⋏
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
  let zeroPairResource := transparentHybridConjunctionPayloadEnvelope
    repeatZeroValuation zeroEqFormula sameFormula
    (compactUnifiedParserSyntaxRepeatNativeEqPayloadPolynomial repeatCount 0)
    (compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable
      width tokenCount witness.tailBoundary witness.tailCount
      next.tasksBoundary next.tasksCount hsame)
  transparentHybridDisjunctionLeftPayloadEnvelope repeatZeroValuation
    zeroBranchFormula positiveBranchFormula zeroPairResource

theorem
    compactUnifiedParserSyntaxRepeatZeroBranchGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount) :
    compactUnifiedParserSyntaxRepeatZeroBranchGraphPayloadEnvelope tokenTable
        width tokenCount next binderArity repeatCount witness hsame <=
      compactUnifiedParserSyntaxRepeatZeroBranchPublicFinitePayloadEnvelope
        tokenTable width tokenCount next binderArity repeatCount witness := by
  unfold compactUnifiedParserSyntaxRepeatZeroBranchGraphPayloadEnvelope
    compactUnifiedParserSyntaxRepeatZeroBranchPublicFinitePayloadEnvelope
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount witness.tailBoundary witness.tailCount
        next.tasksBoundary next.tasksCount hsame))

noncomputable def
    compactUnifiedParserSyntaxRepeatPositiveBranchGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount witness.tailBoundary
      witness.tailCount 2)
    (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0)
    (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
      witness.decrementedCount) : Nat :=
  let zeroEqFormula := nativeEqFormula repeatCount 0
  let sameFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount witness.tailBoundary witness.tailCount
    next.tasksBoundary next.tasksCount
  let zeroBranchFormula := zeroEqFormula ⋏ sameFormula
  let successorEqFormula := nativeSuccessorEqFormula repeatCount
    witness.decrementedCount
  let dropFormula := compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
    witness.tailBoundary witness.tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
  let positiveBranchFormula := successorEqFormula ⋏
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
  let taskPairResource := transparentHybridConjunctionPayloadEnvelope
    atRowsZeroValuation taskZeroFormula taskOneFormula
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 0
      binderArity 0 (fixedNumeralTerm 0) (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) htaskZero)
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 2
      binderArity witness.decrementedCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount) htaskOne)
  let dropTailResource := transparentHybridConjunctionPayloadEnvelope
    dropZeroValuation dropFormula (taskZeroFormula ⋏ taskOneFormula)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      witness.tailBoundary witness.tailCount 2 hdrop)
    taskPairResource
  let positiveResource := transparentHybridConjunctionPayloadEnvelope
    repeatZeroValuation successorEqFormula
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
    (compactUnifiedParserSyntaxRepeatNativeSuccessorEqPayloadPolynomial
      repeatCount witness.decrementedCount)
    dropTailResource
  transparentHybridDisjunctionRightPayloadEnvelope repeatZeroValuation
    zeroBranchFormula positiveBranchFormula positiveResource

theorem
    compactUnifiedParserSyntaxRepeatPositiveBranchGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount witness.tailBoundary
      witness.tailCount 2)
    (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0)
    (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
      witness.decrementedCount) :
    compactUnifiedParserSyntaxRepeatPositiveBranchGraphPayloadEnvelope
        tokenTable width tokenCount next binderArity repeatCount witness hdrop
        htaskZero htaskOne <=
      compactUnifiedParserSyntaxRepeatPositiveBranchPublicFinitePayloadEnvelope
        tokenTable width tokenCount next binderArity repeatCount witness := by
  unfold compactUnifiedParserSyntaxRepeatPositiveBranchGraphPayloadEnvelope
    compactUnifiedParserSyntaxRepeatPositiveBranchPublicFinitePayloadEnvelope
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          witness.tailBoundary witness.tailCount 2 hdrop)
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 0
            binderArity 0 (fixedNumeralTerm 0) (fixedNumeralTerm 0)
            (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
            htaskZero)
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 2
            binderArity witness.decrementedCount (fixedNumeralTerm 1)
            (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm witness.decrementedCount) htaskOne))))

def compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : Nat :=
  let currentFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let nextFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let unconsFormula :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      binderArity repeatCount (fixedNumeralTerm 2)
  let zeroEqFormula := nativeEqFormula repeatCount 0
  let sameFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount witness.tailBoundary witness.tailCount
    next.tasksBoundary next.tasksCount
  let zeroBranchFormula := zeroEqFormula ⋏ sameFormula
  let successorEqFormula := nativeSuccessorEqFormula repeatCount
    witness.decrementedCount
  let dropFormula := compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
    witness.tailBoundary witness.tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
  let positiveBranchFormula := successorEqFormula ⋏
    (dropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula))
  let branchFormula := zeroBranchFormula ⋎ positiveBranchFormula
  let branchResource :=
    compactUnifiedParserSyntaxRepeatZeroBranchPublicFinitePayloadEnvelope
        tokenTable width tokenCount next binderArity repeatCount witness +
      compactUnifiedParserSyntaxRepeatPositiveBranchPublicFinitePayloadEnvelope
        tokenTable width tokenCount next binderArity repeatCount witness
  let unconsBranchResource := transparentHybridConjunctionPayloadEnvelope
    unconsZeroValuation unconsFormula branchFormula
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 2
      binderArity repeatCount (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm repeatCount))
    branchResource
  let tokensTailResource := transparentHybridConjunctionPayloadEnvelope
    natListZeroValuation tokensFormula (unconsFormula ⋏ branchFormula)
    (compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount)
    unconsBranchResource
  let nextTailResource := transparentHybridConjunctionPayloadEnvelope
    binaryStatusZeroValuation nextFormula
    (tokensFormula ⋏ (unconsFormula ⋏ branchFormula))
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    tokensTailResource
  transparentHybridConjunctionPayloadEnvelope binaryStatusZeroValuation
    currentFormula
    (nextFormula ⋏ (tokensFormula ⋏ (unconsFormula ⋏ branchFormula)))
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount current.tasksFinish current.finish)
    nextTailResource

theorem
    compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (branchData : CompactSyntaxRepeatCheckedBranchData tokenTable width
      tokenCount next binderArity repeatCount witness) :
    compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope tokenTable
        width tokenCount current next binderArity repeatCount witness hcurrent
        hnext htokens huncons branchData <=
      compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity repeatCount witness := by
  have htokensResource :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  have hunconsResource :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 2
      binderArity repeatCount (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm repeatCount) huncons
  rcases branchData with ⟨hrepeatZero, hsame⟩ |
    ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
  · have hzero :=
      compactUnifiedParserSyntaxRepeatZeroBranchGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount next binderArity repeatCount witness hsame
    have hbranch :
        compactUnifiedParserSyntaxRepeatZeroBranchGraphPayloadEnvelope tokenTable
            width tokenCount next binderArity repeatCount witness hsame <=
          compactUnifiedParserSyntaxRepeatZeroBranchPublicFinitePayloadEnvelope
              tokenTable width tokenCount next binderArity repeatCount witness +
            compactUnifiedParserSyntaxRepeatPositiveBranchPublicFinitePayloadEnvelope
              tokenTable width tokenCount next binderArity repeatCount
              witness := by
      omega
    unfold compactUnifiedParserSyntaxRepeatZeroBranchGraphPayloadEnvelope at hbranch
    unfold compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope
      compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope
    simp only
    exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          htokensResource
          (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
            hunconsResource hbranch)))
  · have hpositive :=
      compactUnifiedParserSyntaxRepeatPositiveBranchGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount next binderArity repeatCount witness hdrop
        htaskZero htaskOne
    have hbranch :
        compactUnifiedParserSyntaxRepeatPositiveBranchGraphPayloadEnvelope
            tokenTable width tokenCount next binderArity repeatCount witness
            hdrop htaskZero htaskOne <=
          compactUnifiedParserSyntaxRepeatZeroBranchPublicFinitePayloadEnvelope
              tokenTable width tokenCount next binderArity repeatCount witness +
            compactUnifiedParserSyntaxRepeatPositiveBranchPublicFinitePayloadEnvelope
              tokenTable width tokenCount next binderArity repeatCount
              witness := by
      omega
    unfold compactUnifiedParserSyntaxRepeatPositiveBranchGraphPayloadEnvelope at hbranch
    unfold compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope
      compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope
    simp only
    exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          htokensResource
          (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
            hunconsResource hbranch)))

theorem
    compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (branchData : CompactSyntaxRepeatCheckedBranchData tokenTable width
      tokenCount next binderArity repeatCount witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData
          tokenTable width tokenCount current next binderArity repeatCount
          witness hcurrent hnext htokens huncons branchData) ≤
      compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope tokenTable
        width tokenCount current next binderArity repeatCount witness hcurrent
        hnext htokens huncons branchData := by
  let currentCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hcurrent
  let nextCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hnext
  let tokensCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  let unconsCertificate :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 2
      binderArity repeatCount (fixedNumeralTerm 2) (fun valuation => by simp)
      huncons
  have hcurrentResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tasksFinish current.finish hcurrent
  have hnextResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksFinish next.finish hnext
  have htokensResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  have hunconsResource :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 2
      binderArity repeatCount (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm repeatCount)
      (fixedNumeralTerm_freeVariables_eq_empty 2)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty repeatCount)
      (fun valuation => by simp)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) huncons
  rcases branchData with ⟨hrepeatZero, hsame⟩ |
    ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
  ·
    let sameCertificate :=
      compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount witness.tailBoundary witness.tailCount
        next.tasksBoundary next.tasksCount hsame
    let zeroEqCertificate := nativeEqCertificate repeatCount 0 hrepeatZero
    let zeroPair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      zeroEqCertificate sameCertificate
    let branch := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := nativeSuccessorEqFormula repeatCount witness.decrementedCount ⋏
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
          width tokenCount next.tasksBoundary next.tasksCount
          witness.tailBoundary witness.tailCount 2 ⋏
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
              width tokenCount next.tasksBoundary next.tasksCount
              (fixedNumeralTerm 0) (fixedNumeralTerm 0)
              (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) ⋏
            compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
              width tokenCount next.tasksBoundary next.tasksCount
              (fixedNumeralTerm 1) (fixedNumeralTerm 2)
              (shortBinaryNumeralTerm binderArity)
              (shortBinaryNumeralTerm witness.decrementedCount)))) zeroPair
    have hsameResource :=
      compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount witness.tailBoundary witness.tailCount
        next.tasksBoundary next.tasksCount hsame
    have hzeroEqResource :=
      nativeEqCertificate_structuralPayloadBound_le_public repeatCount 0
        hrepeatZero
    have hzeroPair := transparentHybridConjunctionPayloadBound_le
      zeroEqCertificate sameCertificate _ _ hzeroEqResource hsameResource
    have hbranchResource := transparentHybridDisjunctionLeftPayloadBound_le
      (right := nativeSuccessorEqFormula repeatCount witness.decrementedCount ⋏
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
          width tokenCount next.tasksBoundary next.tasksCount
          witness.tailBoundary witness.tailCount 2 ⋏
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
              width tokenCount next.tasksBoundary next.tasksCount
              (fixedNumeralTerm 0) (fixedNumeralTerm 0)
              (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) ⋏
            compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
              width tokenCount next.tasksBoundary next.tasksCount
              (fixedNumeralTerm 1) (fixedNumeralTerm 2)
              (shortBinaryNumeralTerm binderArity)
              (shortBinaryNumeralTerm witness.decrementedCount))))
      zeroPair _ hzeroPair
    let unconsBranch :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        unconsCertificate branch
    have hunconsBranch := transparentHybridConjunctionPayloadBound_le
      unconsCertificate branch _ _ hunconsResource hbranchResource
    let tokensTail :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        tokensCertificate unconsBranch
    have htokensTail := transparentHybridConjunctionPayloadBound_le
      tokensCertificate unconsBranch _ _ htokensResource hunconsBranch
    let nextTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      nextCertificate tokensTail
    have hnextTail := transparentHybridConjunctionPayloadBound_le
      nextCertificate tokensTail _ _ hnextResource htokensTail
    let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      currentCertificate nextTail
    have hparts := transparentHybridConjunctionPayloadBound_le
      currentCertificate nextTail _ _ hcurrentResource hnextTail
    unfold compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData
    simp only
    change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.cast
          (compactUnifiedParserSyntaxRepeatClosedFormula_alignment tokenTable
            width tokenCount current next binderArity repeatCount witness).symm
          parts) ≤ _
    unfold compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope
    simp only
    simpa only [hybridFormulaStructuralPayloadBound, currentCertificate,
      nextCertificate, tokensCertificate, unconsCertificate,
      sameCertificate, zeroEqCertificate, zeroPair, branch, unconsBranch,
      tokensTail, nextTail, parts] using hparts
  ·
    let dropCertificate :=
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        witness.tailBoundary witness.tailCount 2 hdrop
    let taskZeroCertificate :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        0 0 binderArity 0 (fixedNumeralTerm 0) (fixedNumeralTerm 0)
        (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
        (by simp) (fun valuation => by simp) (fun valuation => by
          simp [termValue_shortBinaryNumeralTerm]) (fun valuation => by simp)
        htaskZero
    let taskOneCertificate :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        1 2 binderArity witness.decrementedCount (fixedNumeralTerm 1)
        (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm witness.decrementedCount) (by simp)
        (fun valuation => by simp) (fun valuation => by
          simp [termValue_shortBinaryNumeralTerm]) (fun valuation => by
          simp [termValue_shortBinaryNumeralTerm]) htaskOne
    let successorCertificate := nativeSuccessorEqCertificate repeatCount
      witness.decrementedCount hrepeatSuccessor
    have hdropResource :=
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        witness.tailBoundary witness.tailCount 2 hdrop
    have htaskZeroResource :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        0 0 binderArity 0 (fixedNumeralTerm 0) (fixedNumeralTerm 0)
        (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
        (fixedNumeralTerm_freeVariables_eq_empty 0)
        (fixedNumeralTerm_freeVariables_eq_empty 0)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
        (fixedNumeralTerm_freeVariables_eq_empty 0) (by simp)
        (fun valuation => by simp) (fun valuation => by
          simp [termValue_shortBinaryNumeralTerm]) (fun valuation => by simp)
        htaskZero
    have htaskOneResource :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        1 2 binderArity witness.decrementedCount (fixedNumeralTerm 1)
        (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm witness.decrementedCount)
        (fixedNumeralTerm_freeVariables_eq_empty 1)
        (fixedNumeralTerm_freeVariables_eq_empty 2)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty
          witness.decrementedCount) (by simp) (fun valuation => by simp)
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        htaskOne
    have hsuccessorResource :=
      nativeSuccessorEqCertificate_structuralPayloadBound_le_public
        repeatCount witness.decrementedCount hrepeatSuccessor
    let taskPair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      taskZeroCertificate taskOneCertificate
    have htaskPair := transparentHybridConjunctionPayloadBound_le
      taskZeroCertificate taskOneCertificate _ _ htaskZeroResource
      htaskOneResource
    let dropTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      dropCertificate taskPair
    have hdropTail := transparentHybridConjunctionPayloadBound_le
      dropCertificate taskPair _ _ hdropResource htaskPair
    let positivePair :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        successorCertificate dropTail
    have hpositivePair := transparentHybridConjunctionPayloadBound_le
      successorCertificate dropTail _ _ hsuccessorResource hdropTail
    let branch := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := nativeEqFormula repeatCount 0 ⋏
        compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
          tokenCount witness.tailBoundary witness.tailCount
          next.tasksBoundary next.tasksCount) positivePair
    have hbranchResource := transparentHybridDisjunctionRightPayloadBound_le
      (left := nativeEqFormula repeatCount 0 ⋏
        compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
          tokenCount witness.tailBoundary witness.tailCount
          next.tasksBoundary next.tasksCount)
      positivePair _ hpositivePair
    let unconsBranch :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        unconsCertificate branch
    have hunconsBranch := transparentHybridConjunctionPayloadBound_le
      unconsCertificate branch _ _ hunconsResource hbranchResource
    let tokensTail :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        tokensCertificate unconsBranch
    have htokensTail := transparentHybridConjunctionPayloadBound_le
      tokensCertificate unconsBranch _ _ htokensResource hunconsBranch
    let nextTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      nextCertificate tokensTail
    have hnextTail := transparentHybridConjunctionPayloadBound_le
      nextCertificate tokensTail _ _ hnextResource htokensTail
    let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      currentCertificate nextTail
    have hparts := transparentHybridConjunctionPayloadBound_le
      currentCertificate nextTail _ _ hcurrentResource hnextTail
    unfold compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData
    simp only
    change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.cast
          (compactUnifiedParserSyntaxRepeatClosedFormula_alignment tokenTable
            width tokenCount current next binderArity repeatCount witness).symm
          parts) ≤ _
    unfold compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope
    simp only
    simpa only [hybridFormulaStructuralPayloadBound, currentCertificate,
      nextCertificate, tokensCertificate, unconsCertificate,
      dropCertificate, taskZeroCertificate, taskOneCertificate,
      successorCertificate, taskPair, dropTail, positivePair, branch,
      unconsBranch, tokensTail, nextTail, parts] using hparts

theorem
    compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next binderArity repeatCount witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next binderArity repeatCount
          witness hgraph) ≤
      compactUnifiedParserSyntaxRepeatGraphPayloadEnvelope tokenTable width
        tokenCount current next binderArity repeatCount witness hgraph := by
  simpa only [compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph,
    compactUnifiedParserSyntaxRepeatGraphPayloadEnvelope] using
    compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next binderArity repeatCount witness
      hgraph.1 hgraph.2.1 hgraph.2.2.1 hgraph.2.2.2.1
      (compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
        next binderArity repeatCount witness hgraph.2.2.2.2)

theorem compactUnifiedParserSyntaxRepeatGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next binderArity repeatCount witness) :
    compactUnifiedParserSyntaxRepeatGraphPayloadEnvelope tokenTable width
        tokenCount current next binderArity repeatCount witness hgraph <=
      compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity repeatCount witness := by
  simpa only [compactUnifiedParserSyntaxRepeatGraphPayloadEnvelope] using
    compactUnifiedParserSyntaxRepeatFromGraphDataPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next binderArity repeatCount witness
      hgraph.1 hgraph.2.1 hgraph.2.2.1 hgraph.2.2.2.1
      (compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
        next binderArity repeatCount witness hgraph.2.2.2.2)

theorem
    compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next binderArity repeatCount witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next binderArity repeatCount
          witness hgraph) <=
      compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity repeatCount witness := by
  exact
    (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next binderArity repeatCount witness
      hgraph).trans
    (compactUnifiedParserSyntaxRepeatGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next binderArity repeatCount witness
      hgraph)

#print axioms nativeEqCertificate_structuralPayloadBound_le_public
#print axioms nativeSuccessorEqCertificate_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds
