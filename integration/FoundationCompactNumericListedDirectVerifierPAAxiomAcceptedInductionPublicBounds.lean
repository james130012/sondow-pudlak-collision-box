import integration.FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight
import integration.FoundationCompactNumericListedDirectVerifierCombinePublicBounds

/-!
# Original-input public bounds for an accepted induction PA leaf

The canonical 259-coordinate PA environment was already bounded by its fully
expanded deterministic rule stream.  This file composes that theorem with the
accepted-induction rule-stream bound, so the resulting public coordinate
budget depends only on the three original PA-leaf inputs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectCertificateNodeFixedPAPublicBounds
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAPublicBounds
open FoundationCompactNumericListedDirectCertificateNodeInductionPAPublicBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight

theorem compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound left <=
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound right := by
  have hfuel := compactNumericCertificateParserFuelWeightBound_mono h
  have hwidth :
      compactNumericVerifierPAAxiomJointLeafRuleWidthBound left <=
        compactNumericVerifierPAAxiomJointLeafRuleWidthBound right := by
    unfold compactNumericVerifierPAAxiomJointLeafRuleWidthBound
    omega
  have htable := Nat.mul_le_mul h hwidth
  have hlist := Nat.mul_le_mul (Nat.add_le_add_right h 1) h
  have hstate := Nat.mul_le_mul (Nat.add_le_add_right hfuel 2) h
  have htransform := compactFormulaTransformCanonicalTableWidthBound_mono
    hwidth h hfuel
  have htransform' :
      compactNumericVerifierPAAxiomJointLeafRuleTransformTableWidthBound left <=
        compactNumericVerifierPAAxiomJointLeafRuleTransformTableWidthBound right := by
    simpa [compactNumericVerifierPAAxiomJointLeafRuleTransformTableWidthBound,
      compactNumericVerifierPAAxiomJointLeafRuleWidthBound,
      compactNumericVerifierPAAxiomJointLeafRuleFuelBound] using htransform
  unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    compactNumericVerifierPAAxiomJointLeafRuleTableSizeBound
    compactNumericVerifierPAAxiomJointLeafRuleWidthBound
    compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
    compactNumericVerifierPAAxiomJointLeafRuleStateBoundarySizeBound
    compactNumericVerifierPAAxiomJointLeafRuleFuelBound at *
  omega

private theorem compactCertificateNodeFixedPAPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeFixedPAPublicCoordinateSizeBound left <=
      compactCertificateNodeFixedPAPublicCoordinateSizeBound right := by
  have htoken : 4 * left <= 4 * right := by omega
  have hwidth : 2 * (4 * left) <= 2 * (4 * right) := by omega
  have htable := Nat.mul_le_mul htoken hwidth
  have hboundary := Nat.mul_le_mul (Nat.add_le_add_right h 1) htoken
  unfold compactCertificateNodeFixedPAPublicCoordinateSizeBound
    compactCertificateNodeFixedPAEndpointSizeBound
    compactCertificateNodeFixedPABoundarySizeBound
    compactCertificateNodeFixedPATableSizeBound
    compactCertificateNodeFixedPAWidthBound
    compactCertificateNodeFixedPATokenWeightBound at *
  omega

private theorem compactCertificateNodeSymbolPAPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeSymbolPAPublicCoordinateSizeBound left <=
      compactCertificateNodeSymbolPAPublicCoordinateSizeBound right := by
  have htoken : 4 * left <= 4 * right := by omega
  have hwidth : 2 * (4 * left) <= 2 * (4 * right) := by omega
  have htable := Nat.mul_le_mul htoken hwidth
  have hboundary := Nat.mul_le_mul (Nat.add_le_add_right h 1) htoken
  unfold compactCertificateNodeSymbolPAPublicCoordinateSizeBound
    compactCertificateNodeSymbolPAEndpointSizeBound
    compactCertificateNodeSymbolPAHiddenCoordinateSizeBound
    compactCertificateNodeSymbolPABoundarySizeBound
    compactCertificateNodeSymbolPATableSizeBound
    compactCertificateNodeSymbolPAWidthBound
    compactCertificateNodeSymbolPATokenWeightBound at *
  omega

private theorem compactCertificateNodeInductionPAPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeInductionPAPublicCoordinateSizeBound left <=
      compactCertificateNodeInductionPAPublicCoordinateSizeBound right := by
  have hfuel := compactNumericCertificateParserFuelWeightBound_mono h
  have htrace := compactNumericRootSyntaxParserTraceWeightBound_mono h
  have htoken :
      compactCertificateNodeInductionPATokenWeightBound left <=
        compactCertificateNodeInductionPATokenWeightBound right := by
    unfold compactCertificateNodeInductionPATokenWeightBound
      compactCertificateNodeInductionPATraceWeightBound
    omega
  have hwidth :
      compactCertificateNodeInductionPAWidthBound left <=
        compactCertificateNodeInductionPAWidthBound right := by
    unfold compactCertificateNodeInductionPAWidthBound
    omega
  have htable := Nat.mul_le_mul htoken hwidth
  have hlist := Nat.mul_le_mul (Nat.add_le_add_right h 1) htoken
  have hstate := Nat.mul_le_mul (Nat.add_le_add_right hfuel 2) htoken
  have htokenArea := Nat.mul_le_mul
    (Nat.add_le_add_right htoken 1) htoken
  have hparserStep :
      compactCertificateNodeInductionPAParserStepWidthBound left <=
        compactCertificateNodeInductionPAParserStepWidthBound right := by
    unfold compactCertificateNodeInductionPAParserStepWidthBound
    omega
  have hfuelColumns := Nat.mul_le_mul_right
    compactParserSyntaxAdjacentStepWitnessColumnCount hfuel
  have hparserRows := Nat.mul_le_mul hfuelColumns hparserStep
  have hparserTail := Nat.mul_le_mul_left 23 hparserStep
  have hparserTable :
      compactCertificateNodeInductionPAParserTableWidthBound left <=
        compactCertificateNodeInductionPAParserTableWidthBound right := by
    unfold compactCertificateNodeInductionPAParserTableWidthBound
      compactCertificateNodeInductionPAFuelBound
    omega
  unfold compactCertificateNodeInductionPAPublicCoordinateSizeBound
    compactCertificateNodeInductionPAEndpointSizeBound
    compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    compactCertificateNodeInductionPAParserTableWidthBound
    compactCertificateNodeInductionPAParserStepWidthBound
    compactCertificateNodeInductionPAStateBoundarySizeBound
    compactCertificateNodeInductionPAListBoundarySizeBound
    compactCertificateNodeInductionPATableSizeBound
    compactCertificateNodeInductionPAWidthBound
    compactCertificateNodeInductionPATokenWeightBound
    compactCertificateNodeInductionPATraceWeightBound
    compactCertificateNodeInductionPAFuelBound at *
  omega

theorem compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound left <=
      compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound right := by
  have hfixed := compactCertificateNodeFixedPAPublicCoordinateSizeBound_mono h
  have hsymbol := compactCertificateNodeSymbolPAPublicCoordinateSizeBound_mono h
  have hinduction :=
    compactCertificateNodeInductionPAPublicCoordinateSizeBound_mono h
  unfold compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
  omega

def compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound
    (originalWeight : Nat) : Nat :=
  compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      (compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial
        originalWeight) +
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
      (originalWeight + 4)

theorem
    compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound_mono
    {left right : Nat} (hweight : left <= right) :
    compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound
        left <=
      compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound
        right := by
  have hrulePolynomial :=
    compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial_mono
      hweight
  have hrule :=
    compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound_mono
      hrulePolynomial
  have hendpoint :=
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound_mono
      (Nat.add_le_add_right hweight 4)
  unfold compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound
  omega

/-- One branch-independent envelope for every accepted PA leaf.  The extra
`originalWeight` summand covers the three-chunk non-induction rule stream;
the induction branch uses the stronger polynomial proved in the imported
module. -/
def compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound
    (originalWeight : Nat) : Nat :=
  compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      (compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial
          originalWeight + originalWeight) +
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
      (originalWeight + 4)

theorem compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound_mono
    {left right : Nat} (hweight : left <= right) :
    compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound left <=
      compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound right := by
  have hpolynomial :=
    compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial_mono
      hweight
  have hinput :
      compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial left +
          left <=
        compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial right +
          right :=
    Nat.add_le_add hpolynomial hweight
  have hrule :=
    compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound_mono hinput
  have hendpoint :=
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound_mono
      (Nat.add_le_add_right hweight 4)
  unfold compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound
  omega

theorem compactNumericVerifierPAAxiomJointLeafEndpointInputWeight_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    compactNumericVerifierPAAxiomJointLeafEndpointInputWeight certificate <=
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate certificate + 4 := by
  let certificateTokens := compactPAAxiomCertificateTokens certificate
  have happend := compactAdditiveValueWeight_list_append_le
    ([1] : List Nat) certificateTokens
  have hone : compactAdditiveValueWeight ([1] : List Nat) = 4 := by
    decide
  have hcertificate :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_certificate_le
      Gamma candidate certificate
  have hcertificate' :
      compactAdditiveValueWeight certificateTokens <=
        compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          Gamma candidate certificate := by
    simpa [certificateTokens] using hcertificate
  unfold compactNumericVerifierPAAxiomJointLeafEndpointInputWeight
  change compactAdditiveValueWeight ([1] ++ certificateTokens) <= _
  rw [hone] at happend
  omega

theorem compactNumericVerifierPAAxiomJointLeafRuleInputWeight_fixed_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    compactNumericVerifierPAAxiomJointLeafRuleInputWeight
        Gamma candidate certificate <=
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate certificate := by
  unfold compactNumericVerifierPAAxiomJointLeafRuleInputWeight
    compactNumericVerifierPAAxiomJointLeafCanonicalRuleTokens
  rw [compactPAAxiomLeafRuleRowsCanonicalChunks_eq_fixed
    Gamma candidate certificate hfixed]
  simp only [compactFixedPAAxiomLeafRuleRowsCanonicalChunks,
    List.flatten_cons, List.flatten_nil, List.append_nil,
    compactAdditiveTokenWeight_append]
  change compactAdditiveValueWeight Gamma +
      (compactAdditiveValueWeight
          (compactPAAxiomCertificateTokens certificate) +
        compactAdditiveValueWeight (compactSentenceTokens candidate)) <= _
  unfold compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
  omega

theorem compactNumericVerifierPAAxiomJointLeafEndpointInputWeight_induction_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactNumericVerifierPAAxiomJointLeafEndpointInputWeight
        (.induction body) <=
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate (.induction body) + 4 := by
  let certificateTokens := compactPAAxiomCertificateTokens (.induction body)
  have happend := compactAdditiveValueWeight_list_append_le
    ([1] : List Nat) certificateTokens
  have hone : compactAdditiveValueWeight ([1] : List Nat) = 4 := by
    decide
  have hcertificate :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_certificate_le
      Gamma candidate (.induction body)
  have hcertificate' :
      compactAdditiveValueWeight certificateTokens <=
        compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          Gamma candidate (.induction body) := by
    simpa [certificateTokens] using hcertificate
  unfold compactNumericVerifierPAAxiomJointLeafEndpointInputWeight
  change compactAdditiveValueWeight ([1] ++ certificateTokens) <= _
  rw [hone] at happend
  omega

theorem compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound_induction_le_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
        Gamma candidate (.induction body) <=
      compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound
        (compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          Gamma candidate (.induction body)) := by
  have hrule :=
    compactNumericVerifierPAAxiomJointLeafRuleInputWeight_induction_le_of_accept
      Gamma candidate body haccept
  have hruleCoordinate :=
    compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound_mono hrule
  have hendpoint :=
    compactNumericVerifierPAAxiomJointLeafEndpointInputWeight_induction_le
      Gamma candidate body
  have hendpointCoordinate :=
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound_mono
      hendpoint
  unfold compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
    compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound
  exact Nat.add_le_add hruleCoordinate hendpointCoordinate

theorem compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound_le_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens certificate)) = true) :
    compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
        Gamma candidate certificate <=
      compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound
        (compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          Gamma candidate certificate) := by
  let originalWeight := compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
    Gamma candidate certificate
  have hendpoint :=
    compactNumericVerifierPAAxiomJointLeafEndpointInputWeight_le
      Gamma candidate certificate
  have hendpointCoordinate :=
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound_mono
      hendpoint
  by_cases hfixed : FixedPAAxiomCertificate certificate
  · have hrule :=
      compactNumericVerifierPAAxiomJointLeafRuleInputWeight_fixed_le
        Gamma candidate certificate hfixed
    have hruleTarget :
        compactNumericVerifierPAAxiomJointLeafRuleInputWeight
            Gamma candidate certificate <=
          compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial
              originalWeight + originalWeight := by
      exact hrule.trans (Nat.le_add_left _ _)
    have hruleCoordinate :=
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound_mono
        hruleTarget
    unfold compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
      compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound
    exact Nat.add_le_add hruleCoordinate hendpointCoordinate
  · have hinduction : exists body, certificate = .induction body := by
      cases certificate <;>
        simp_all [FixedPAAxiomCertificate]
    rcases hinduction with ⟨body, rfl⟩
    have hrule :=
      compactNumericVerifierPAAxiomJointLeafRuleInputWeight_induction_le_of_accept
        Gamma candidate body haccept
    have hruleTarget :
        compactNumericVerifierPAAxiomJointLeafRuleInputWeight
            Gamma candidate (.induction body) <=
          compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial
              originalWeight + originalWeight := by
      exact hrule.trans (Nat.le_add_right _ _)
    have hruleCoordinate :=
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound_mono
        hruleTarget
    unfold compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
      compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound
    exact Nat.add_le_add hruleCoordinate hendpointCoordinate

theorem CompactNumericVerifierPAAxiomJointLeafRows.exists_inductionCanonical_with_acceptedOriginalPublicBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    exists c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate (.induction body) c /\
      forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <=
        compactNumericVerifierPAAxiomAcceptedInductionPublicCoordinateSizeBound
          (compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
            Gamma candidate (.induction body)) := by
  rcases
      CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical_with_publicBounds
        Gamma candidate (.induction body) with
    ⟨c, hcanonical, hbounds⟩
  refine ⟨c, hcanonical, ?_⟩
  intro coordinate
  exact (hbounds coordinate).trans
    (compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound_induction_le_of_accept
      Gamma candidate body haccept)

theorem CompactNumericVerifierPAAxiomJointLeafRows.exists_acceptedCanonical_with_originalPublicBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens certificate)) = true) :
    exists c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate certificate c /\
      forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <=
        compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound
          (compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
            Gamma candidate certificate) := by
  rcases
      CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical_with_publicBounds
        Gamma candidate certificate with
    ⟨c, hcanonical, hbounds⟩
  refine ⟨c, hcanonical, ?_⟩
  intro coordinate
  exact (hbounds coordinate).trans
    (compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound_le_of_accept
      Gamma candidate certificate haccept)

#print axioms
  compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound_induction_le_of_accept
#print axioms
  compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound_le_of_accept
#print axioms
  CompactNumericVerifierPAAxiomJointLeafRows.exists_inductionCanonical_with_acceptedOriginalPublicBounds
#print axioms
  CompactNumericVerifierPAAxiomJointLeafRows.exists_acceptedCanonical_with_originalPublicBounds

end FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionPublicBounds
