import integration.FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness
import integration.FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck

/-!
# Canonical completeness for the induction PA-axiom rule check

The guarded induction route, the certificate payload, the candidate sentence,
and the ambient sequent are encoded in one fixed-width token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectInductionPAAxiomRuleCheckCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
open FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness

def compactInductionPAAxiomRuleCheckExtraChunks
    (bodyTokens candidateTokens : List Nat) (Gamma : List (List Nat)) :
    List (List Nat) :=
  [compactAdditiveEncode (22 :: bodyTokens),
    compactAdditiveEncode candidateTokens,
    compactAdditiveEncode Gamma]

def compactInductionPAAxiomRuleCheckChunks
    (bodyTokens candidateTokens : List Nat) (Gamma : List (List Nat)) :
    List (List Nat) :=
  compactGuardedInductionRouteChunks
      (compactGuardedInductionExecutableData bodyTokens) ++
    compactInductionPAAxiomRuleCheckExtraChunks
      bodyTokens candidateTokens Gamma

@[simp] theorem compactInductionPAAxiomRuleCheckChunks_length
    (bodyTokens candidateTokens : List Nat) (Gamma : List (List Nat)) :
    (compactInductionPAAxiomRuleCheckChunks
      bodyTokens candidateTokens Gamma).length = 40 := by
  simp [compactInductionPAAxiomRuleCheckChunks,
    compactInductionPAAxiomRuleCheckExtraChunks,
    compactGuardedInductionRouteChunks]

@[simp] theorem compactInductionPAAxiomRuleCheckChunks_body
    (bodyTokens candidateTokens : List Nat) (Gamma : List (List Nat)) :
    (compactInductionPAAxiomRuleCheckChunks
      bodyTokens candidateTokens Gamma).getI 0 =
        compactAdditiveEncode bodyTokens := by
  rfl

@[simp] theorem compactInductionPAAxiomRuleCheckChunks_axiom
    (bodyTokens candidateTokens : List Nat) (Gamma : List (List Nat)) :
    (compactInductionPAAxiomRuleCheckChunks
      bodyTokens candidateTokens Gamma).getI 37 =
        compactAdditiveEncode (22 :: bodyTokens) := by
  simp [compactInductionPAAxiomRuleCheckChunks,
    compactInductionPAAxiomRuleCheckExtraChunks,
    compactGuardedInductionRouteChunks]

@[simp] theorem compactInductionPAAxiomRuleCheckChunks_candidate
    (bodyTokens candidateTokens : List Nat) (Gamma : List (List Nat)) :
    (compactInductionPAAxiomRuleCheckChunks
      bodyTokens candidateTokens Gamma).getI 38 =
        compactAdditiveEncode candidateTokens := by
  simp [compactInductionPAAxiomRuleCheckChunks,
    compactInductionPAAxiomRuleCheckExtraChunks,
    compactGuardedInductionRouteChunks]

@[simp] theorem compactInductionPAAxiomRuleCheckChunks_gamma
    (bodyTokens candidateTokens : List Nat) (Gamma : List (List Nat)) :
    (compactInductionPAAxiomRuleCheckChunks
      bodyTokens candidateTokens Gamma).getI 39 =
        compactAdditiveEncode Gamma := by
  simp [compactInductionPAAxiomRuleCheckChunks,
    compactInductionPAAxiomRuleCheckExtraChunks,
    compactGuardedInductionRouteChunks]

def CompactCanonicalInductionPAAxiomRuleCheck
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (Gamma : List (List Nat)) (gammaBoundary : Nat)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) : Prop :=
  let bodyTokens := compactArithmeticFormulaTokens body
  let candidateTokens := compactSentenceTokens candidate
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactInductionPAAxiomRuleCheckChunks
    bodyTokens candidateTokens Gamma
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let resultBoolValue := compactAdditiveBoolTag
    (compactAxmRuleCheck
      (Gamma, (candidateTokens, 22 :: bodyTokens)))
  CompactAdditiveInductionPAAxiomRuleCheck
    tokenTable width tokens.length gammaBoundary Gamma.length resultBoolValue
    (compactPackedNatListSlot chunks 37 (22 :: bodyTokens))
    (compactPackedNatListSlot chunks 0 data.body)
    (compactPackedNatListSlot chunks 1 data.zeroWitness)
    (compactPackedNatListSlot chunks 2 data.openZeroWitness)
    (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
    (compactPackedNatListSlot chunks 4 data.captureOne)
    (compactPackedNatListSlot chunks 5 data.empty)
    (compactPackedNatListSlot chunks 6 data.base)
    (compactPackedNatListSlot chunks 7 data.negatedBase)
    (compactPackedNatListSlot chunks 10 data.stepZero)
    (compactPackedNatListSlot chunks 13 data.stepSuccessor)
    (compactPackedNatListSlot chunks 14 data.negatedStepZero)
    (compactPackedNatListSlot chunks 15 data.stepDisjunction)
    (compactPackedNatListSlot chunks 16 data.quantifiedStep)
    (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
    (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
    (compactPackedNatListSlot chunks 19 data.innerDisjunction)
    (compactPackedNatListSlot chunks 20 data.sentence)
    (compactPackedNatListSlot chunks 21 data.fvarList)
    (compactPackedNatListSlot chunks 22 data.depthCapture)
    (compactPackedNatListSlot chunks 23 data.fixed)
    (compactPackedNatListSlot chunks 24 data.generated)
    (compactPackedNatListSlot chunks 38 candidateTokens)
    data.depth coordinates

set_option maxHeartbeats 700000 in
theorem exists_compactCanonicalInductionPAAxiomRuleCheck
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (Gamma : List (List Nat)) :
    ∃ gammaBoundary coordinates,
      CompactCanonicalInductionPAAxiomRuleCheck
        body candidate Gamma gammaBoundary coordinates := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let candidateTokens := compactSentenceTokens candidate
  let data := compactGuardedInductionExecutableData bodyTokens
  let extraChunks := compactInductionPAAxiomRuleCheckExtraChunks
    bodyTokens candidateTokens Gamma
  let chunks := compactInductionPAAxiomRuleCheckChunks
    bodyTokens candidateTokens Gamma
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let resultBoolValue := compactAdditiveBoolTag
    (compactAxmRuleCheck
      (Gamma, (candidateTokens, 22 :: bodyTokens)))
  change ∃ gammaBoundary coordinates,
    CompactAdditiveInductionPAAxiomRuleCheck
      tokenTable width tokens.length gammaBoundary Gamma.length
      resultBoolValue
      (compactPackedNatListSlot chunks 37 (22 :: bodyTokens))
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated)
      (compactPackedNatListSlot chunks 38 candidateTokens)
      data.depth coordinates
  have hchunksLength : chunks.length = 40 := by
    simpa [chunks] using compactInductionPAAxiomRuleCheckChunks_length
      bodyTokens candidateTokens Gamma
  have hlength : 40 <= chunks.length := by omega
  have slotCanonical (index : Nat) (values : List Nat)
      (hindex : index < chunks.length)
      (hchunk : chunks[index] = compactAdditiveEncode values) :
      CompactPackedNatListSlotCanonical tokenTable width tokens.length
        (compactPackedNatListSlot chunks index values) values := by
    simpa [tokenTable, width, tokens] using
      compactPackedNatListSlot_canonical chunks index values hindex hchunk
  have hbody : CompactPackedNatListSlotCanonical
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 0 bodyTokens) bodyTokens :=
    slotCanonical 0 bodyTokens (by omega) (by
      rw [← List.getI_eq_getElem chunks (by omega)]
      simpa [chunks] using compactInductionPAAxiomRuleCheckChunks_body
        bodyTokens candidateTokens Gamma)
  have haxiom : CompactPackedNatListSlotCanonical
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 37 (22 :: bodyTokens))
      (22 :: bodyTokens) :=
    slotCanonical 37 (22 :: bodyTokens) (by omega) (by
      rw [← List.getI_eq_getElem chunks (by omega)]
      simpa [chunks] using compactInductionPAAxiomRuleCheckChunks_axiom
        bodyTokens candidateTokens Gamma)
  have hcandidate : CompactPackedNatListSlotCanonical
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 38 candidateTokens)
      candidateTokens :=
    slotCanonical 38 candidateTokens (by omega) (by
      rw [← List.getI_eq_getElem chunks (by omega)]
      simpa [chunks] using compactInductionPAAxiomRuleCheckChunks_candidate
        bodyTokens candidateTokens Gamma)
  have hgammaLayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length
      (compactPackedChunkPrefix chunks 39).length
      ((compactPackedChunkPrefix chunks 39).length +
        (compactAdditiveEncode Gamma).length) Gamma := by
    simpa [tokenTable, width, tokens] using
      compactPackedNatListListLayout_canonical chunks 39 Gamma
        (by omega) (by
          rw [← List.getI_eq_getElem chunks (by omega)]
          simpa [chunks] using compactInductionPAAxiomRuleCheckChunks_gamma
            bodyTokens candidateTokens Gamma)
  rcases hgammaLayout with
    ⟨gammaBoundary, _hgammaStructure, hgammaRows, _hgammaSize⟩
  have hconsLength : CompactAdditiveNatListConsRows
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 0 bodyTokens).boundary
      bodyTokens.length
      (compactPackedNatListSlot chunks 37 (22 :: bodyTokens)).boundary
      (22 :: bodyTokens).length 22 :=
    (compactAdditiveNatListConsRows_iff_cons_of_rows
      hbody.elements haxiom.elements).2 rfl
  have hcons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 0 bodyTokens).boundary
      (compactPackedNatListSlot chunks 0 bodyTokens).count
      (compactPackedNatListSlot chunks 37 (22 :: bodyTokens)).boundary
      (compactPackedNatListSlot chunks 37 (22 :: bodyTokens)).count 22 := by
    simpa only [hbody.1, haxiom.1] using hconsLength
  rcases exists_compactGuardedInductionSentenceRoute_of_executable_body
      bodyTokens extraChunks with
    ⟨coordinates, hroute⟩
  have hrule : CompactAdditiveInductionPAAxiomRuleCheck
      tokenTable width tokens.length gammaBoundary Gamma.length
      resultBoolValue
      (compactPackedNatListSlot chunks 37 (22 :: bodyTokens))
      (compactPackedNatListSlot chunks 0 bodyTokens)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated)
      (compactPackedNatListSlot chunks 38 candidateTokens)
      data.depth coordinates :=
    (compactAdditiveInductionPAAxiomRuleCheck_iff_of_route
      (resultBoolValue := resultBoolValue)
      body candidate hcons hroute hgammaRows hbody.layout
      hcandidate.layout).2 (by
        simp [resultBoolValue, bodyTokens, candidateTokens,
          compactPAAxiomCertificateTokens])
  exact ⟨gammaBoundary, coordinates, hrule⟩

#print axioms exists_compactCanonicalInductionPAAxiomRuleCheck

end FoundationCompactNumericListedDirectInductionPAAxiomRuleCheckCompleteness
