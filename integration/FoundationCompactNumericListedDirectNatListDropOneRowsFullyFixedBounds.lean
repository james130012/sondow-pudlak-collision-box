import integration.FoundationCompactNumericListedDirectNatListDropOneRowsCountLeavesFullyFixedBounds

/-!
# Fully fixed complete drop-one natural-list certificate

The two closed count leaves and the fixed row universal are assembled in the
original right-associated formula.  The row-data and graph endpoints expose
only the shared numeric and bit coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsCountLeavesFullyFixedBounds

private abbrev dropOneRowsZeroValuationFullyFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def dropOneRowsInnerSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let equalityCode :=
    dropOneRowsCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropOneRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  equalityCode + universalCode + 9

def dropOneRowsCompleteSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  dropOneRowsCountBoundFormulaCodePolynomial bitBound +
    dropOneRowsInnerSyntaxFixedPolynomial numericBound bitBound + 9

def dropOneRowsInnerFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound)
    (dropOneRowsCountEqualityFullyFixedPayloadPolynomial bitBound)
    (dropOneRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound)

def dropOneRowsCompleteFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound)
    (dropOneRowsCountBoundFullyFixedPayloadPolynomial bitBound)
    (dropOneRowsInnerFullyFixedPayloadPolynomial numericBound bitBound)

private theorem dropOneRowsUniversalFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      targetCount : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).ballLT
        (shortBinaryNumeralTerm targetCount) =
      ∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm targetCount))
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 1) := by
  rw [LO.FirstOrder.Semiformula.ballLT,
    LO.FirstOrder.Semiformula.ball_eq]
  unfold termBoundedUniversalBody termBoundFormula
  rw [finiteCaseLessThanFormula_eq_operator]

theorem
    compactAdditiveNatListDropOneRowsClosedFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        1)).length <=
      dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 1) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 1) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).ballLT
        (shortBinaryNumeralTerm targetCount)
  let equalityCode :=
    dropOneRowsCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropOneRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  let innerCode :=
    dropOneRowsInnerSyntaxFixedPolynomial numericBound bitBound
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <=
        dropOneRowsCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact dropOneRowsCountBoundFormula_code_length_le_fixed sourceCount
      bitBound hsourceCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= equalityCode := by
    dsimp only [countEqualityFormula, equalityCode]
    exact dropOneRowsCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hbody :
      (binaryFormulaCode
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 1)).length <=
        dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveNatListDropOneRowsBody_code_length_le_fixed tokenTable width
      tokenCount sourceBoundary targetBoundary numericBound bitBound hwidth
      htokenCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= universalCode := by
    have huniversalAlignment :
        universalFormula =
          ∀⁰ termBoundedUniversalBody
            (Rew.bShift (shortBinaryNumeralTerm targetCount))
            (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
              tokenCount sourceBoundary targetBoundary 1) := by
      dsimp only [universalFormula]
      exact dropOneRowsUniversalFormula_alignment tokenTable width tokenCount
        sourceBoundary targetBoundary targetCount
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 1)
        targetCount numericBound bitBound
        (dropOneRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
        (dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
        htargetCountSize hbody
    rw [huniversalAlignment]
    exact hraw
  have hinnerRaw :=
    binaryFormulaCode_and_length_le countEqualityFormula universalFormula
  have hinner :
      (binaryFormulaCode
        (countEqualityFormula ⋏ universalFormula)).length <= innerCode := by
    unfold innerCode dropOneRowsInnerSyntaxFixedPolynomial
    dsimp only [equalityCode, universalCode]
    omega
  have htotalRaw := binaryFormulaCode_and_length_le countBoundFormula
    (countEqualityFormula ⋏ universalFormula)
  rw [compactAdditiveNatListDropFixedNumeralRowsClosedFormula_alignment]
  unfold compactAdditiveNatListDropFixedNumeralRowsExplicitFormula
  change
    (binaryFormulaCode
      (countBoundFormula ⋏
        (countEqualityFormula ⋏ universalFormula))).length <= _
  unfold dropOneRowsCompleteSyntaxFixedPolynomial
  exact htotalRaw.trans (by omega)

theorem
    compactAdditiveNatListDropOneRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
      1).freeVariables = ∅ := by
  rw [compactAdditiveNatListDropFixedNumeralRowsClosedFormula_alignment]
  unfold compactAdditiveNatListDropFixedNumeralRowsExplicitFormula
  rw [dropOneRowsUniversalFormula_alignment]
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveNatListDropOneRowsOuterFormula_freeVariables_eq_empty,
    dropOneRowsCountBoundFormula_freeVariables_eq_empty,
    dropOneRowsCountEqualityFormula_freeVariables_eq_empty]
  simp

theorem
    compactAdditiveNatListDropOneRowsFromRowDataPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveNatListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount 1 rows <=
      dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 1) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 1) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).ballLT
        (shortBinaryNumeralTerm targetCount)
  let innerFormula := countEqualityFormula ⋏ universalFormula
  let countBoundResource :=
    compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
      1 sourceCount
  let countEqualityResource :=
    compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
      sourceCount 1 targetCount
  let universalResource :=
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      1 rows
  let countBoundFixed :=
    dropOneRowsCountBoundFullyFixedPayloadPolynomial bitBound
  let countEqualityFixed :=
    dropOneRowsCountEqualityFullyFixedPayloadPolynomial bitBound
  let universalFixed :=
    dropOneRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound
  let innerFixed :=
    dropOneRowsInnerFullyFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropOneRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  have hsyntaxResource :
      syntaxResource =
        dropOneRowsCountBoundFormulaCodePolynomial bitBound +
          (dropOneRowsCountEqualityFormulaCodePolynomial bitBound +
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
    exact dropOneRowsCountBoundPayloadPolynomial_le_fullyFixed sourceCount
      bitBound hsourceCountSize
  have hcountEquality :
      countEqualityResource <= countEqualityFixed := by
    dsimp only [countEqualityResource, countEqualityFixed]
    exact dropOneRowsCountEqualityPayloadPolynomial_le_fullyFixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have huniversal :
      universalResource <= universalFixed := by
    dsimp only [universalResource, universalFixed]
    exact
      compactAdditiveNatListDropOneRowsUniversalPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph rows hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
        hnumericSize
  have hboundClosed : countBoundFormula.freeVariables = ∅ := by
    dsimp only [countBoundFormula]
    exact dropOneRowsCountBoundFormula_freeVariables_eq_empty sourceCount
  have hequalityClosed : countEqualityFormula.freeVariables = ∅ := by
    dsimp only [countEqualityFormula]
    exact dropOneRowsCountEqualityFormula_freeVariables_eq_empty sourceCount
      targetCount
  have huniversalAlignment :
      universalFormula =
        ∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm targetCount))
          (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary 1) := by
    exact dropOneRowsUniversalFormula_alignment tokenTable width tokenCount
      sourceBoundary targetBoundary targetCount
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    rw [huniversalAlignment]
    exact compactAdditiveNatListDropOneRowsOuterFormula_freeVariables_eq_empty
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
  have hinnerClosed : innerFormula.freeVariables = ∅ := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
      huniversalClosed]
    simp
  have hboundCodeFixed :
      (binaryFormulaCode countBoundFormula).length <=
        dropOneRowsCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact dropOneRowsCountBoundFormula_code_length_le_fixed
      sourceCount bitBound hsourceCountSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <= syntaxResource := by
    exact hboundCodeFixed.trans (by
      rw [hsyntaxResource]
      omega)
  have hequalityCodeFixed :
      (binaryFormulaCode countEqualityFormula).length <=
        dropOneRowsCountEqualityFormulaCodePolynomial bitBound := by
    dsimp only [countEqualityFormula]
    exact dropOneRowsCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= syntaxResource := by
    exact hequalityCodeFixed.trans (by
    rw [hsyntaxResource]
    omega)
  have hbody :=
    compactAdditiveNatListDropOneRowsBody_code_length_le_fixed tokenTable width
      tokenCount sourceBoundary targetBoundary numericBound bitBound hwidth
      htokenCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have huniversalCodeRaw :=
    closedShortTermBoundedUniversalFormula_code_length_le_source
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 1)
      targetCount numericBound bitBound
      (dropOneRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
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
        dropOneRowsInnerSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [innerFormula]
    rw [show
      dropOneRowsInnerSyntaxFixedPolynomial numericBound bitBound =
        dropOneRowsCountEqualityFormulaCodePolynomial bitBound +
          universalCode + 9 by rfl]
    exact hinnerRaw.trans (by
      dsimp only [universalCode] at huniversalCodeBound
      omega)
  have hinnerCode :
      (binaryFormulaCode innerFormula).length <= syntaxResource := by
    exact hinnerCodeFixed.trans (by
      rw [hsyntaxResource]
      unfold dropOneRowsInnerSyntaxFixedPolynomial
      dsimp only [universalCode]
      omega)
  have htotalRaw := binaryFormulaCode_and_length_le countBoundFormula
    innerFormula
  have htotalCode :
      (binaryFormulaCode
        (countBoundFormula ⋏ innerFormula)).length <= syntaxResource := by
    exact htotalRaw.trans (by
      rw [hsyntaxResource]
      unfold dropOneRowsInnerSyntaxFixedPolynomial at hinnerCodeFixed
      dsimp only [universalCode] at hinnerCodeFixed
      omega)
  have hsyntaxPositive : 1 <= syntaxResource := by
    rw [hsyntaxResource]
    omega
  let equalityUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope
      dropOneRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityResource universalResource
  have hinnerMono :
      equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          dropOneRowsZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed := by
    dsimp only [equalityUniversalResource]
    exact transparentHybridConjunctionPayloadEnvelope_mono
      dropOneRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      hcountEquality huniversal
  have hinnerClosedBound :
      transparentHybridConjunctionPayloadEnvelope
          dropOneRowsZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed <=
        innerFixed := by
    unfold innerFixed dropOneRowsInnerFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      dropOneRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityFixed universalFixed syntaxResource hsyntaxPositive
      hequalityClosed huniversalClosed hequalityCode huniversalCode hinnerCode
  have hinner : equalityUniversalResource <= innerFixed :=
    hinnerMono.trans hinnerClosedBound
  have houterMono :
      transparentHybridConjunctionPayloadEnvelope
          dropOneRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundResource equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          dropOneRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed :=
    transparentHybridConjunctionPayloadEnvelope_mono
      dropOneRowsZeroValuationFullyFixed countBoundFormula innerFormula
      hcountBound hinner
  have houterClosed :
      transparentHybridConjunctionPayloadEnvelope
          dropOneRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed <=
        dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold dropOneRowsCompleteFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      dropOneRowsZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundFixed innerFixed syntaxResource hsyntaxPositive
      hboundClosed hinnerClosed hboundCode hinnerCode htotalCode
  unfold
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
  change
    transparentHybridConjunctionPayloadEnvelope
      dropOneRowsZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundResource equalityUniversalResource <=
      dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  exact houterMono.trans houterClosed

theorem compactAdditiveNatListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        1 hgraph <=
      dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  unfold compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope
  exact
    compactAdditiveNatListDropOneRowsFromRowDataPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph
      (compactAdditiveNatListDropFixedNumeralRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        1 hgraph)
      hwidth htokenCount hsourceCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize

#print axioms
  compactAdditiveNatListDropOneRowsClosedFormula_code_length_le_fullyFixed
#print axioms
  compactAdditiveNatListDropOneRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveNatListDropOneRowsFromRowDataPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveNatListDropOneRowsGraphPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds
