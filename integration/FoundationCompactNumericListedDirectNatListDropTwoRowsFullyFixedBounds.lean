import integration.FoundationCompactNumericListedDirectNatListDropTwoRowsCountLeavesFullyFixedBounds

/-!
# Fully fixed complete drop-two natural-list certificate

The two closed count leaves and the fixed row universal are assembled in the
original right-associated formula.  The row-data and graph endpoints expose
only the shared numeric and bit coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropTwoRowsFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListDropTwoRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListDropTwoRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropTwoRowsUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropTwoRowsCountLeavesFullyFixedBounds

private abbrev dropTwoRowsZeroValuationFullyFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def dropTwoRowsInnerSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let equalityCode :=
    dropTwoRowsCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropTwoRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  equalityCode + universalCode + 9

def dropTwoRowsCompleteSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  dropTwoRowsCountBoundFormulaCodePolynomial bitBound +
    dropTwoRowsInnerSyntaxFixedPolynomial numericBound bitBound + 9

def dropTwoRowsInnerFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (dropTwoRowsCompleteSyntaxFixedPolynomial numericBound bitBound)
    (dropTwoRowsCountEqualityFullyFixedPayloadPolynomial bitBound)
    (dropTwoRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound)

def dropTwoRowsCompleteFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (dropTwoRowsCompleteSyntaxFixedPolynomial numericBound bitBound)
    (dropTwoRowsCountBoundFullyFixedPayloadPolynomial bitBound)
    (dropTwoRowsInnerFullyFixedPayloadPolynomial numericBound bitBound)

private theorem dropTwoRowsUniversalFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      targetCount : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 2).ballLT
        (shortBinaryNumeralTerm targetCount) =
      ∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm targetCount))
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 2) := by
  rw [LO.FirstOrder.Semiformula.ballLT,
    LO.FirstOrder.Semiformula.ball_eq]
  unfold termBoundedUniversalBody termBoundFormula
  rw [finiteCaseLessThanFormula_eq_operator]

theorem
    compactAdditiveNatListDropTwoRowsClosedFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2)
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
        2)).length <=
      dropTwoRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 2) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 2) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 2).ballLT
        (shortBinaryNumeralTerm targetCount)
  let equalityCode :=
    dropTwoRowsCountEqualityFormulaCodePolynomial bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropTwoRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  let innerCode :=
    dropTwoRowsInnerSyntaxFixedPolynomial numericBound bitBound
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <=
        dropTwoRowsCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact dropTwoRowsCountBoundFormula_code_length_le_fixed sourceCount
      bitBound hsourceCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= equalityCode := by
    dsimp only [countEqualityFormula, equalityCode]
    exact dropTwoRowsCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hbody :
      (binaryFormulaCode
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 2)).length <=
        dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveNatListDropTwoRowsBody_code_length_le_fixed tokenTable width
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
              tokenCount sourceBoundary targetBoundary 2) := by
      dsimp only [universalFormula]
      exact dropTwoRowsUniversalFormula_alignment tokenTable width tokenCount
        sourceBoundary targetBoundary targetCount
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source
        (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary 2)
        targetCount numericBound bitBound
        (dropTwoRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
        (dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
        htargetCountSize hbody
    rw [huniversalAlignment]
    exact hraw
  have hinnerRaw :=
    binaryFormulaCode_and_length_le countEqualityFormula universalFormula
  have hinner :
      (binaryFormulaCode
        (countEqualityFormula ⋏ universalFormula)).length <= innerCode := by
    unfold innerCode dropTwoRowsInnerSyntaxFixedPolynomial
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
  unfold dropTwoRowsCompleteSyntaxFixedPolynomial
  exact htotalRaw.trans (by omega)

theorem
    compactAdditiveNatListDropTwoRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
      2).freeVariables = ∅ := by
  rw [compactAdditiveNatListDropFixedNumeralRowsClosedFormula_alignment]
  unfold compactAdditiveNatListDropFixedNumeralRowsExplicitFormula
  rw [dropTwoRowsUniversalFormula_alignment]
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveNatListDropTwoRowsOuterFormula_freeVariables_eq_empty,
    dropTwoRowsCountBoundFormula_freeVariables_eq_empty,
    dropTwoRowsCountEqualityFormula_freeVariables_eq_empty]
  simp

theorem
    compactAdditiveNatListDropTwoRowsFromRowDataPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveNatListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 2 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount 2 rows <=
      dropTwoRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm 2) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 2) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 2).ballLT
        (shortBinaryNumeralTerm targetCount)
  let innerFormula := countEqualityFormula ⋏ universalFormula
  let countBoundResource :=
    compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
      2 sourceCount
  let countEqualityResource :=
    compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
      sourceCount 2 targetCount
  let universalResource :=
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      2 rows
  let countBoundFixed :=
    dropTwoRowsCountBoundFullyFixedPayloadPolynomial bitBound
  let countEqualityFixed :=
    dropTwoRowsCountEqualityFullyFixedPayloadPolynomial bitBound
  let universalFixed :=
    dropTwoRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound
  let innerFixed :=
    dropTwoRowsInnerFullyFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    dropTwoRowsCompleteSyntaxFixedPolynomial numericBound bitBound
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (dropTwoRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  have hsyntaxResource :
      syntaxResource =
        dropTwoRowsCountBoundFormulaCodePolynomial bitBound +
          (dropTwoRowsCountEqualityFormulaCodePolynomial bitBound +
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
    exact dropTwoRowsCountBoundPayloadPolynomial_le_fullyFixed sourceCount
      bitBound hsourceCountSize
  have hcountEquality :
      countEqualityResource <= countEqualityFixed := by
    dsimp only [countEqualityResource, countEqualityFixed]
    exact dropTwoRowsCountEqualityPayloadPolynomial_le_fullyFixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have huniversal :
      universalResource <= universalFixed := by
    dsimp only [universalResource, universalFixed]
    exact
      compactAdditiveNatListDropTwoRowsUniversalPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph rows hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
        hnumericSize
  have hboundClosed : countBoundFormula.freeVariables = ∅ := by
    dsimp only [countBoundFormula]
    exact dropTwoRowsCountBoundFormula_freeVariables_eq_empty sourceCount
  have hequalityClosed : countEqualityFormula.freeVariables = ∅ := by
    dsimp only [countEqualityFormula]
    exact dropTwoRowsCountEqualityFormula_freeVariables_eq_empty sourceCount
      targetCount
  have huniversalAlignment :
      universalFormula =
        ∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm targetCount))
          (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary 2) := by
    exact dropTwoRowsUniversalFormula_alignment tokenTable width tokenCount
      sourceBoundary targetBoundary targetCount
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    rw [huniversalAlignment]
    exact compactAdditiveNatListDropTwoRowsOuterFormula_freeVariables_eq_empty
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
  have hinnerClosed : innerFormula.freeVariables = ∅ := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
      huniversalClosed]
    simp
  have hboundCodeFixed :
      (binaryFormulaCode countBoundFormula).length <=
        dropTwoRowsCountBoundFormulaCodePolynomial bitBound := by
    dsimp only [countBoundFormula]
    exact dropTwoRowsCountBoundFormula_code_length_le_fixed
      sourceCount bitBound hsourceCountSize
  have hboundCode :
      (binaryFormulaCode countBoundFormula).length <= syntaxResource := by
    exact hboundCodeFixed.trans (by
      rw [hsyntaxResource]
      omega)
  have hequalityCodeFixed :
      (binaryFormulaCode countEqualityFormula).length <=
        dropTwoRowsCountEqualityFormulaCodePolynomial bitBound := by
    dsimp only [countEqualityFormula]
    exact dropTwoRowsCountEqualityFormula_code_length_le_fixed sourceCount
      targetCount bitBound hsourceCountSize htargetCountSize
  have hequalityCode :
      (binaryFormulaCode countEqualityFormula).length <= syntaxResource := by
    exact hequalityCodeFixed.trans (by
    rw [hsyntaxResource]
    omega)
  have hbody :=
    compactAdditiveNatListDropTwoRowsBody_code_length_le_fixed tokenTable width
      tokenCount sourceBoundary targetBoundary numericBound bitBound hwidth
      htokenCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have huniversalCodeRaw :=
    closedShortTermBoundedUniversalFormula_code_length_le_source
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 2)
      targetCount numericBound bitBound
      (dropTwoRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
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
        dropTwoRowsInnerSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [innerFormula]
    rw [show
      dropTwoRowsInnerSyntaxFixedPolynomial numericBound bitBound =
        dropTwoRowsCountEqualityFormulaCodePolynomial bitBound +
          universalCode + 9 by rfl]
    exact hinnerRaw.trans (by
      dsimp only [universalCode] at huniversalCodeBound
      omega)
  have hinnerCode :
      (binaryFormulaCode innerFormula).length <= syntaxResource := by
    exact hinnerCodeFixed.trans (by
      rw [hsyntaxResource]
      unfold dropTwoRowsInnerSyntaxFixedPolynomial
      dsimp only [universalCode]
      omega)
  have htotalRaw := binaryFormulaCode_and_length_le countBoundFormula
    innerFormula
  have htotalCode :
      (binaryFormulaCode
        (countBoundFormula ⋏ innerFormula)).length <= syntaxResource := by
    exact htotalRaw.trans (by
      rw [hsyntaxResource]
      unfold dropTwoRowsInnerSyntaxFixedPolynomial at hinnerCodeFixed
      dsimp only [universalCode] at hinnerCodeFixed
      omega)
  have hsyntaxPositive : 1 <= syntaxResource := by
    rw [hsyntaxResource]
    omega
  let equalityUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope
      dropTwoRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityResource universalResource
  have hinnerMono :
      equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          dropTwoRowsZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed := by
    dsimp only [equalityUniversalResource]
    exact transparentHybridConjunctionPayloadEnvelope_mono
      dropTwoRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      hcountEquality huniversal
  have hinnerClosedBound :
      transparentHybridConjunctionPayloadEnvelope
          dropTwoRowsZeroValuationFullyFixed countEqualityFormula
          universalFormula countEqualityFixed universalFixed <=
        innerFixed := by
    unfold innerFixed dropTwoRowsInnerFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      dropTwoRowsZeroValuationFullyFixed countEqualityFormula universalFormula
      countEqualityFixed universalFixed syntaxResource hsyntaxPositive
      hequalityClosed huniversalClosed hequalityCode huniversalCode hinnerCode
  have hinner : equalityUniversalResource <= innerFixed :=
    hinnerMono.trans hinnerClosedBound
  have houterMono :
      transparentHybridConjunctionPayloadEnvelope
          dropTwoRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundResource equalityUniversalResource <=
        transparentHybridConjunctionPayloadEnvelope
          dropTwoRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed :=
    transparentHybridConjunctionPayloadEnvelope_mono
      dropTwoRowsZeroValuationFullyFixed countBoundFormula innerFormula
      hcountBound hinner
  have houterClosed :
      transparentHybridConjunctionPayloadEnvelope
          dropTwoRowsZeroValuationFullyFixed countBoundFormula innerFormula
          countBoundFixed innerFixed <=
        dropTwoRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold dropTwoRowsCompleteFullyFixedPayloadPolynomial
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      dropTwoRowsZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundFixed innerFixed syntaxResource hsyntaxPositive
      hboundClosed hinnerClosed hboundCode hinnerCode htotalCode
  unfold
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
  change
    transparentHybridConjunctionPayloadEnvelope
      dropTwoRowsZeroValuationFullyFixed countBoundFormula innerFormula
      countBoundResource equalityUniversalResource <=
      dropTwoRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  exact houterMono.trans houterClosed

theorem compactAdditiveNatListDropTwoRowsGraphPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        2 hgraph <=
      dropTwoRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  unfold compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope
  exact
    compactAdditiveNatListDropTwoRowsFromRowDataPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph
      (compactAdditiveNatListDropFixedNumeralRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        2 hgraph)
      hwidth htokenCount hsourceCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize

#print axioms
  compactAdditiveNatListDropTwoRowsClosedFormula_code_length_le_fullyFixed
#print axioms
  compactAdditiveNatListDropTwoRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveNatListDropTwoRowsFromRowDataPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveNatListDropTwoRowsGraphPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropTwoRowsFullyFixedBounds
