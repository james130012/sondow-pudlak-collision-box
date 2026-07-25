import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsCountLeavesFullyFixedBounds

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

namespace FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListDropThreeRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsCountLeavesFullyFixedBounds

private abbrev dropThreeRowsZeroValuationFullyFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def dropThreeRowsInnerSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let equalityCode :=
    dropThreeRowsCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropThreeRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  equalityCode + universalCode + 9

def dropThreeRowsCompleteSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  dropThreeRowsCountBoundFormulaCodePolynomial bitBound +
    dropThreeRowsInnerSyntaxFixedPolynomial numericBound bitBound + 9

def dropThreeRowsInnerFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (dropThreeRowsCompleteSyntaxFixedPolynomial numericBound bitBound)
    (dropThreeRowsCountEqualityFullyFixedPayloadPolynomial bitBound)
    (dropThreeRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound)

def dropThreeRowsCompleteFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (dropThreeRowsCompleteSyntaxFixedPolynomial numericBound bitBound)
    (dropThreeRowsCountBoundFullyFixedPayloadPolynomial bitBound)
    (dropThreeRowsInnerFullyFixedPayloadPolynomial numericBound bitBound)

private theorem dropThreeRowsUniversalFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      targetCount : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 3).ballLT
        (shortBinaryNumeralTerm targetCount) =
      ∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm targetCount))
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 3) := by
  rw [LO.FirstOrder.Semiformula.ballLT,
    LO.FirstOrder.Semiformula.ball_eq]
  unfold termBoundedUniversalBody termBoundFormula
  rw [finiteCaseLessThanFormula_eq_operator]

theorem
    compactAdditiveNatListDropThreeRowsClosedFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
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
        3)).length <=
      dropThreeRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 3) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 3) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 3).ballLT
        (shortBinaryNumeralTerm targetCount)
  let equalityCode :=
    dropThreeRowsCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropThreeRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  let innerCode :=
    dropThreeRowsInnerSyntaxFixedPolynomial numericBound bitBound
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <=
        dropThreeRowsCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact dropThreeRowsCountBoundFormula_code_length_le_fixed sourceCount
      bitBound hsourceCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= equalityCode := by
    dsimp only [countEqualityFormula, equalityCode]
    exact dropThreeRowsCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hbody :
      (binaryFormulaCode
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 3)).length <=
        dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveNatListDropThreeRowsBody_code_length_le_fixed tokenTable width
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
              tokenCount sourceBoundary targetBoundary 3) := by
      dsimp only [universalFormula]
      exact dropThreeRowsUniversalFormula_alignment tokenTable width tokenCount
        sourceBoundary targetBoundary targetCount
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 3)
        targetCount numericBound bitBound
        (dropThreeRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
        (dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
        htargetCountSize hbody
    rw [huniversalAlignment]
    exact hraw
  have hinnerRaw :=
    binaryFormulaCode_and_length_le countEqualityFormula universalFormula
  have hinner :
      (binaryFormulaCode
        (countEqualityFormula ⋏ universalFormula)).length <= innerCode := by
    unfold innerCode dropThreeRowsInnerSyntaxFixedPolynomial
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
  unfold dropThreeRowsCompleteSyntaxFixedPolynomial
  exact htotalRaw.trans (by omega)

theorem
    compactAdditiveNatListDropThreeRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
      3).freeVariables = ∅ := by
  rw [compactAdditiveNatListDropFixedNumeralRowsClosedFormula_alignment]
  unfold compactAdditiveNatListDropFixedNumeralRowsExplicitFormula
  rw [dropThreeRowsUniversalFormula_alignment]
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveNatListDropThreeRowsOuterFormula_freeVariables_eq_empty,
    dropThreeRowsCountBoundFormula_freeVariables_eq_empty,
    dropThreeRowsCountEqualityFormula_freeVariables_eq_empty]
  simp

theorem
    compactAdditiveNatListDropThreeRowsFromRowDataPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveNatListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 3 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount 3 rows <=
      dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 3) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 3) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 3).ballLT
        (shortBinaryNumeralTerm targetCount)
  let innerFormula := countEqualityFormula ⋏ universalFormula
  let countBoundResource :=
    compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
      3 sourceCount
  let countEqualityResource :=
    compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
      sourceCount 3 targetCount
  let universalResource :=
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      3 rows
  let countBoundFixed :=
    dropThreeRowsCountBoundFullyFixedPayloadPolynomial bitBound
  let countEqualityFixed :=
    dropThreeRowsCountEqualityFullyFixedPayloadPolynomial bitBound
  let universalFixed :=
    dropThreeRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound
  let innerFixed :=
    dropThreeRowsInnerFullyFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    dropThreeRowsCompleteSyntaxFixedPolynomial numericBound bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropThreeRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  have hsyntaxResource :
      syntaxResource =
        dropThreeRowsCountBoundFormulaCodePolynomial bitBound +
          (dropThreeRowsCountEqualityFormulaCodePolynomial bitBound +
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
    exact dropThreeRowsCountBoundPayloadPolynomial_le_fullyFixed sourceCount
      bitBound hsourceCountSize
  have hcountEquality :
      countEqualityResource <= countEqualityFixed := by
    dsimp only [countEqualityResource, countEqualityFixed]
    exact dropThreeRowsCountEqualityPayloadPolynomial_le_fullyFixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have huniversal :
      universalResource <= universalFixed := by
    dsimp only [universalResource, universalFixed]
    exact
      compactAdditiveNatListDropThreeRowsUniversalPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph rows hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
        hnumericSize
  have hboundClosed : countBoundFormula.freeVariables = ∅ := by
    dsimp only [countBoundFormula]
    exact dropThreeRowsCountBoundFormula_freeVariables_eq_empty sourceCount
  have hequalityClosed : countEqualityFormula.freeVariables = ∅ := by
    dsimp only [countEqualityFormula]
    exact dropThreeRowsCountEqualityFormula_freeVariables_eq_empty sourceCount
      targetCount
  have huniversalAlignment :
      universalFormula =
        ∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm targetCount))
          (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary 3) := by
    exact dropThreeRowsUniversalFormula_alignment tokenTable width tokenCount
      sourceBoundary targetBoundary targetCount
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    rw [huniversalAlignment]
    exact compactAdditiveNatListDropThreeRowsOuterFormula_freeVariables_eq_empty
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
  have hinnerClosed : innerFormula.freeVariables = ∅ := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
      huniversalClosed]
    simp
  have hboundCodeFixed :
      (binaryFormulaCode countBoundFormula).length <=
        dropThreeRowsCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact dropThreeRowsCountBoundFormula_code_length_le_fixed
      sourceCount bitBound hsourceCountSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <= syntaxResource := by
    exact hboundCodeFixed.trans (by
      rw [hsyntaxResource]
      omega)
  have hequalityCodeFixed :
      (binaryFormulaCode countEqualityFormula).length <=
        dropThreeRowsCountEqualityFormulaCodePolynomial bitBound := by
    dsimp only [countEqualityFormula]
    exact dropThreeRowsCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= syntaxResource := by
    exact hequalityCodeFixed.trans (by
    rw [hsyntaxResource]
    omega)
  have hbody :=
    compactAdditiveNatListDropThreeRowsBody_code_length_le_fixed tokenTable width
      tokenCount sourceBoundary targetBoundary numericBound bitBound hwidth
      htokenCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have huniversalCodeRaw :=
    closedShortTermBoundedUniversalFormula_code_length_le_source
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 3)
      targetCount numericBound bitBound
      (dropThreeRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
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
        dropThreeRowsInnerSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [innerFormula]
    rw [show
      dropThreeRowsInnerSyntaxFixedPolynomial numericBound bitBound =
        dropThreeRowsCountEqualityFormulaCodePolynomial bitBound +
          universalCode + 9 by rfl]
    exact hinnerRaw.trans (by
      dsimp only [universalCode] at huniversalCodeBound
      omega)
  have hinnerCode :
      (binaryFormulaCode innerFormula).length <= syntaxResource := by
    exact hinnerCodeFixed.trans (by
      rw [hsyntaxResource]
      unfold dropThreeRowsInnerSyntaxFixedPolynomial
      dsimp only [universalCode]
      omega)
  have htotalRaw := binaryFormulaCode_and_length_le countBoundFormula
    innerFormula
  have htotalCode :
      (binaryFormulaCode
        (countBoundFormula ⋏ innerFormula)).length <= syntaxResource := by
    exact htotalRaw.trans (by
      rw [hsyntaxResource]
      unfold dropThreeRowsInnerSyntaxFixedPolynomial at hinnerCodeFixed
      dsimp only [universalCode] at hinnerCodeFixed
      omega)
  have hsyntaxPositive : 1 <= syntaxResource := by
    rw [hsyntaxResource]
    omega
  let equalityUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope
      dropThreeRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityResource universalResource
  have hinnerMono :
      equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          dropThreeRowsZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed := by
    dsimp only [equalityUniversalResource]
    exact transparentHybridConjunctionPayloadEnvelope_mono
      dropThreeRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      hcountEquality huniversal
  have hinnerClosedBound :
      transparentHybridConjunctionPayloadEnvelope
          dropThreeRowsZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed <=
        innerFixed := by
    unfold innerFixed dropThreeRowsInnerFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      dropThreeRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityFixed universalFixed syntaxResource hsyntaxPositive
      hequalityClosed huniversalClosed hequalityCode huniversalCode hinnerCode
  have hinner : equalityUniversalResource <= innerFixed :=
    hinnerMono.trans hinnerClosedBound
  have houterMono :
      transparentHybridConjunctionPayloadEnvelope
          dropThreeRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundResource equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          dropThreeRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed :=
    transparentHybridConjunctionPayloadEnvelope_mono
      dropThreeRowsZeroValuationFullyFixed countBoundFormula innerFormula
      hcountBound hinner
  have houterClosed :
      transparentHybridConjunctionPayloadEnvelope
          dropThreeRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed <=
        dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold dropThreeRowsCompleteFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      dropThreeRowsZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundFixed innerFixed syntaxResource hsyntaxPositive
      hboundClosed hinnerClosed hboundCode hinnerCode htotalCode
  unfold
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
  change
    transparentHybridConjunctionPayloadEnvelope
      dropThreeRowsZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundResource equalityUniversalResource <=
      dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  exact houterMono.trans houterClosed

theorem compactAdditiveNatListDropThreeRowsGraphPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        3 hgraph <=
      dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  unfold compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope
  exact
    compactAdditiveNatListDropThreeRowsFromRowDataPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph
      (compactAdditiveNatListDropFixedNumeralRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        3 hgraph)
      hwidth htokenCount hsourceCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize

#print axioms
  compactAdditiveNatListDropThreeRowsClosedFormula_code_length_le_fullyFixed
#print axioms
  compactAdditiveNatListDropThreeRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveNatListDropThreeRowsFromRowDataPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveNatListDropThreeRowsGraphPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds
