import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsCountLeavesFullyFixedBounds

/-!
# Fully fixed complete drop-two syntax-task-list certificate

The two closed count leaves and the fixed row universal are assembled in the
original right-associated formula.  The row-data and graph endpoints expose
only the shared numeric and bit coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsCountLeavesFullyFixedBounds

private abbrev taskDropOneZeroValuationFullyFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def taskDropOneInnerSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let equalityCode :=
    taskDropOneCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (taskDropOneUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound)
  equalityCode + universalCode + 9

def taskDropOneCompleteSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  taskDropOneCountBoundFormulaCodePolynomial bitBound +
    taskDropOneInnerSyntaxFixedPolynomial numericBound bitBound + 9

def taskDropOneInnerFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (taskDropOneCompleteSyntaxFixedPolynomial numericBound bitBound)
    (taskDropOneCountEqualityFullyFixedPayloadPolynomial bitBound)
    (taskDropOneUniversalFullyFixedPayloadPolynomial numericBound bitBound)

def taskDropOneCompleteFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (taskDropOneCompleteSyntaxFixedPolynomial numericBound bitBound)
    (taskDropOneCountBoundFullyFixedPayloadPolynomial bitBound)
    (taskDropOneInnerFullyFixedPayloadPolynomial numericBound bitBound)

private theorem taskDropOneUniversalFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      targetCount : Nat) :
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).ballLT
        (shortBinaryNumeralTerm targetCount) =
      ∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm targetCount))
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 1) := by
  rw [LO.FirstOrder.Semiformula.ballLT,
    LO.FirstOrder.Semiformula.ball_eq]
  unfold termBoundedUniversalBody termBoundFormula
  rw [finiteCaseLessThanFormula_eq_operator]

theorem
    compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        1)).length <=
      taskDropOneCompleteSyntaxFixedPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 1) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 1) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).ballLT
        (shortBinaryNumeralTerm targetCount)
  let equalityCode :=
    taskDropOneCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (taskDropOneUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound)
  let innerCode :=
    taskDropOneInnerSyntaxFixedPolynomial numericBound bitBound
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <=
        taskDropOneCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact taskDropOneCountBoundFormula_code_length_le_fixed sourceCount
      bitBound hsourceCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= equalityCode := by
    dsimp only [countEqualityFormula, equalityCode]
    exact taskDropOneCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 1)).length <=
        taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveSyntaxTaskListDropOneRowsBody_code_length_le_fixed tokenTable width
      tokenCount sourceBoundary targetBoundary numericBound bitBound
      htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= universalCode := by
    have huniversalAlignment :
        universalFormula =
          ∀⁰ termBoundedUniversalBody
            (Rew.bShift (shortBinaryNumeralTerm targetCount))
            (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
              tokenCount sourceBoundary targetBoundary 1) := by
      dsimp only [universalFormula]
      exact taskDropOneUniversalFormula_alignment tokenTable width tokenCount
        sourceBoundary targetBoundary targetCount
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 1)
        targetCount numericBound bitBound
        (taskDropOneUniversalSyntaxFixedPolynomial numericBound bitBound)
        (taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound)
        htargetCountSize hbody
    rw [huniversalAlignment]
    exact hraw
  have hinnerRaw :=
    binaryFormulaCode_and_length_le countEqualityFormula universalFormula
  have hinner :
      (binaryFormulaCode
        (countEqualityFormula ⋏ universalFormula)).length <= innerCode := by
    unfold innerCode taskDropOneInnerSyntaxFixedPolynomial
    dsimp only [equalityCode, universalCode]
    omega
  have htotalRaw := binaryFormulaCode_and_length_le countBoundFormula
    (countEqualityFormula ⋏ universalFormula)
  rw [compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula_alignment]
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitFormula
  change
    (binaryFormulaCode
      (countBoundFormula ⋏
        (countEqualityFormula ⋏ universalFormula))).length <= _
  unfold taskDropOneCompleteSyntaxFixedPolynomial
  exact htotalRaw.trans (by omega)

theorem
    compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount : Nat) :
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
      1).freeVariables = ∅ := by
  rw [compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula_alignment]
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitFormula
  rw [taskDropOneUniversalFormula_alignment]
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveSyntaxTaskListDropOneRowsOuterFormula_freeVariables_eq_empty_fixed,
    taskDropOneCountBoundFormula_freeVariables_eq_empty,
    taskDropOneCountEqualityFormula_freeVariables_eq_empty]
  simp

theorem
    compactAdditiveSyntaxTaskListDropOneRowsFromRowDataPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount 1 rows <=
      taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 1) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 1) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).ballLT
        (shortBinaryNumeralTerm targetCount)
  let innerFormula := countEqualityFormula ⋏ universalFormula
  let countBoundResource :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsCountBoundPayloadPolynomial
      1 sourceCount
  let countEqualityResource :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsCountEqualityPayloadPolynomial
      sourceCount 1 targetCount
  let universalResource :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      1 rows
  let countBoundFixed :=
    taskDropOneCountBoundFullyFixedPayloadPolynomial bitBound
  let countEqualityFixed :=
    taskDropOneCountEqualityFullyFixedPayloadPolynomial bitBound
  let universalFixed :=
    taskDropOneUniversalFullyFixedPayloadPolynomial numericBound bitBound
  let innerFixed :=
    taskDropOneInnerFullyFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    taskDropOneCompleteSyntaxFixedPolynomial numericBound bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (taskDropOneUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound)
  have hsyntaxResource :
      syntaxResource =
        taskDropOneCountBoundFormulaCodePolynomial bitBound +
          (taskDropOneCountEqualityFormulaCodePolynomial bitBound +
            universalCode + 9) + 9 := by
    rfl
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hcountBound :
      countBoundResource <= countBoundFixed := by
    dsimp only [countBoundResource, countBoundFixed]
    exact taskDropOneCountBoundPayloadPolynomial_le_fullyFixed sourceCount
      bitBound hsourceCountSize
  have hcountEquality :
      countEqualityResource <= countEqualityFixed := by
    dsimp only [countEqualityResource, countEqualityFixed]
    exact taskDropOneCountEqualityPayloadPolynomial_le_fullyFixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have huniversal :
      universalResource <= universalFixed := by
    dsimp only [universalResource, universalFixed]
    exact
      compactAdditiveSyntaxTaskListDropOneRowsUniversalPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph rows hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
        hnumericSize
  have hboundClosed : countBoundFormula.freeVariables = ∅ := by
    dsimp only [countBoundFormula]
    exact taskDropOneCountBoundFormula_freeVariables_eq_empty sourceCount
  have hequalityClosed : countEqualityFormula.freeVariables = ∅ := by
    dsimp only [countEqualityFormula]
    exact taskDropOneCountEqualityFormula_freeVariables_eq_empty sourceCount
      targetCount
  have huniversalAlignment :
      universalFormula =
        ∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm targetCount))
          (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary 1) := by
    exact taskDropOneUniversalFormula_alignment tokenTable width tokenCount
      sourceBoundary targetBoundary targetCount
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    rw [huniversalAlignment]
    exact compactAdditiveSyntaxTaskListDropOneRowsOuterFormula_freeVariables_eq_empty_fixed
      tokenTable width tokenCount sourceBoundary targetCount targetBoundary
  have hinnerClosed : innerFormula.freeVariables = ∅ := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
      huniversalClosed]
    simp
  have hboundCodeFixed :
      (binaryFormulaCode countBoundFormula).length <=
        taskDropOneCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact taskDropOneCountBoundFormula_code_length_le_fixed
      sourceCount bitBound hsourceCountSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <= syntaxResource := by
    exact hboundCodeFixed.trans (by
      rw [hsyntaxResource]
      omega)
  have hequalityCodeFixed :
      (binaryFormulaCode countEqualityFormula).length <=
        taskDropOneCountEqualityFormulaCodePolynomial bitBound := by
    dsimp only [countEqualityFormula]
    exact taskDropOneCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= syntaxResource := by
    exact hequalityCodeFixed.trans (by
    rw [hsyntaxResource]
    omega)
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :=
    compactAdditiveSyntaxTaskListDropOneRowsBody_code_length_le_fixed tokenTable width
      tokenCount sourceBoundary targetBoundary numericBound bitBound
      htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have huniversalCodeRaw :=
    closedShortTermBoundedUniversalFormula_code_length_le_source
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 1)
      targetCount numericBound bitBound
      (taskDropOneUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound)
      htargetCountSize hbody
  have huniversalCodeBound :
      (binaryFormulaCode universalFormula).length <= universalCode := by
    rw [huniversalAlignment]
    simpa only [universalCode] using huniversalCodeRaw
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= syntaxResource := by
    exact huniversalCodeBound.trans (by
      rw [hsyntaxResource]
      omega)
  have hinnerRaw :=
    binaryFormulaCode_and_length_le countEqualityFormula universalFormula
  have hinnerCodeFixed :
      (binaryFormulaCode innerFormula).length <=
        taskDropOneInnerSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [innerFormula]
    rw [show
      taskDropOneInnerSyntaxFixedPolynomial numericBound bitBound =
        taskDropOneCountEqualityFormulaCodePolynomial bitBound +
          universalCode + 9 by rfl]
    exact hinnerRaw.trans (by
      dsimp only [universalCode] at huniversalCodeBound
      omega)
  have hinnerCode :
      (binaryFormulaCode innerFormula).length <= syntaxResource := by
    exact hinnerCodeFixed.trans (by
      rw [hsyntaxResource]
      unfold taskDropOneInnerSyntaxFixedPolynomial
      dsimp only [universalCode]
      omega)
  have htotalRaw := binaryFormulaCode_and_length_le countBoundFormula
    innerFormula
  have htotalCode :
      (binaryFormulaCode
        (countBoundFormula ⋏ innerFormula)).length <= syntaxResource := by
    exact htotalRaw.trans (by
      rw [hsyntaxResource]
      unfold taskDropOneInnerSyntaxFixedPolynomial at hinnerCodeFixed
      dsimp only [universalCode] at hinnerCodeFixed
      omega)
  have hsyntaxPositive : 1 <= syntaxResource := by
    rw [hsyntaxResource]
    omega
  let equalityUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope
      taskDropOneZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityResource universalResource
  have hinnerMono :
      equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          taskDropOneZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed := by
    dsimp only [equalityUniversalResource]
    exact transparentHybridConjunctionPayloadEnvelope_mono
      taskDropOneZeroValuationFullyFixed countEqualityFormula universalFormula
      hcountEquality huniversal
  have hinnerClosedBound :
      transparentHybridConjunctionPayloadEnvelope
          taskDropOneZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed <=
        innerFixed := by
    unfold innerFixed taskDropOneInnerFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      taskDropOneZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityFixed universalFixed syntaxResource hsyntaxPositive
      hequalityClosed huniversalClosed hequalityCode huniversalCode hinnerCode
  have hinner : equalityUniversalResource <= innerFixed :=
    hinnerMono.trans hinnerClosedBound
  have houterMono :
      transparentHybridConjunctionPayloadEnvelope
          taskDropOneZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundResource equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          taskDropOneZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed :=
    transparentHybridConjunctionPayloadEnvelope_mono
      taskDropOneZeroValuationFullyFixed countBoundFormula innerFormula
      hcountBound hinner
  have houterClosed :
      transparentHybridConjunctionPayloadEnvelope
          taskDropOneZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed <=
        taskDropOneCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold taskDropOneCompleteFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      taskDropOneZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundFixed innerFixed syntaxResource hsyntaxPositive
      hboundClosed hinnerClosed hboundCode hinnerCode htotalCode
  unfold
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataPayloadEnvelope
  change
    transparentHybridConjunctionPayloadEnvelope
      taskDropOneZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundResource equalityUniversalResource <=
      taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound
  exact houterMono.trans houterClosed

theorem compactAdditiveSyntaxTaskListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        1 hgraph <=
      taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope
  exact
    compactAdditiveSyntaxTaskListDropOneRowsFromRowDataPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        1 hgraph)
      hwidth htokenCount hsourceCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize

#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_code_length_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsFromRowDataPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsGraphPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds
