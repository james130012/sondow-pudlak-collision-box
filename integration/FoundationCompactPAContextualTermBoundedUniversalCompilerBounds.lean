import integration.FoundationCompactPAContextualTermBoundedUniversalCompiler

/-!
# Payload bound for contextual universals with an arbitrary bound term

The logical compiler transports the original bound term to the canonical
finite-exhaustion numeral.  The resource below records every checked proof
operation in that transport and contains no proof-length premise.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAContextualTermBoundedUniversalCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextDischarge
open FoundationCompactCertifiedContextUniversalIntroduction
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAUnaryAtomicTransport

def compileContextualTermBoundedUniversalStructuralPayloadBound
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (boundEquality : CertifiedPAContextProof
      (Gamma.image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 bound) =
        !!(Rew.free boundTerm)” :
        LO.FirstOrder.ArithmeticProposition))
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound) : Nat :=
  let shiftedGamma := Gamma.image Rewriting.shift
  let originalBound := freedTermBoundFormula boundTerm
  let canonicalBound := finiteBoundFormula bound
  let originalContext := insert (∼originalBound) shiftedGamma
  let canonicalImplication :=
    LO.Arrow.arrow canonicalBound (Rewriting.free body)
  let forwardEquality :=
    (“!!(iteratedSuccessorTerm 0 bound) =
      !!(Rew.free boundTerm)” :
      LO.FirstOrder.ArithmeticProposition)
  let backwardEquality :=
    (“!!(Rew.free boundTerm) =
      !!(iteratedSuccessorTerm 0 bound)” :
      LO.FirstOrder.ArithmeticProposition)
  let subjectEquality :=
    (“&0 = &0” : LO.FirstOrder.ArithmeticProposition)
  let underBoundResource :=
    branches.compileUnderBoundAssumptionStructuralPayloadBound
  let canonicalImplicationResource :=
    underBoundResource +
      contextualDischargeFullAssemblyCost shiftedGamma
        canonicalBound (Rewriting.free body)
  let canonicalUnderOriginalResource :=
    canonicalImplicationResource +
      weakeningFullAssemblyCost
        (insert canonicalImplication originalContext)
  let originalAssumptionResource :=
    assumptionFullPayloadCost originalContext originalBound
  let backwardResource :=
    (equalitySymmetryImplication
      (iteratedSuccessorTerm 0 bound)
      (Rew.free boundTerm)).payloadLength +
    weakeningFullAssemblyCost
      (insert (forwardEquality 🡒 backwardEquality) shiftedGamma) +
    boundEquality.payloadLength +
    contextualModusPonensFullAssemblyCost shiftedGamma
      forwardEquality backwardEquality
  let backwardUnderOriginalResource :=
    backwardResource +
      weakeningFullAssemblyCost
        (insert backwardEquality originalContext)
  let subjectResource :=
    (proveEqualityReflexivityAtTerm
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).payloadLength +
    weakeningFullAssemblyCost
      (insert subjectEquality originalContext)
  let transportResource :=
    relationTransportImplicationStructuralPayloadBound
      originalContext Language.ORing.Rel.lt
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (Rew.free boundTerm)
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (iteratedSuccessorTerm 0 bound)
      subjectResource backwardUnderOriginalResource
  let canonicalAssumptionResource :=
    transportResource + originalAssumptionResource +
      contextualModusPonensFullAssemblyCost originalContext
        originalBound canonicalBound
  let bodyUnderOriginalResource :=
    canonicalUnderOriginalResource + canonicalAssumptionResource +
      contextualModusPonensFullAssemblyCost originalContext
        canonicalBound (Rewriting.free body)
  let originalImplicationResource :=
    bodyUnderOriginalResource +
      contextualDischargeFullAssemblyCost shiftedGamma
        originalBound (Rewriting.free body)
  originalImplicationResource +
    contextualUniversalIntroductionFullAssemblyCost Gamma
      (termBoundedUniversalBody boundTerm body)

/-- Numeric envelope used by callers that independently bound the normalized
bound equality and all finite branches. -/
def compileContextualTermBoundedUniversalPayloadEnvelope
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (boundEqualityResource branchResource : Nat) : Nat :=
  let shiftedGamma := Gamma.image Rewriting.shift
  let originalBound := freedTermBoundFormula boundTerm
  let canonicalBound := finiteBoundFormula bound
  let originalContext := insert (∼originalBound) shiftedGamma
  let canonicalImplication :=
    LO.Arrow.arrow canonicalBound (Rewriting.free body)
  let forwardEquality :=
    (“!!(iteratedSuccessorTerm 0 bound) =
      !!(Rew.free boundTerm)” :
      LO.FirstOrder.ArithmeticProposition)
  let backwardEquality :=
    (“!!(Rew.free boundTerm) =
      !!(iteratedSuccessorTerm 0 bound)” :
      LO.FirstOrder.ArithmeticProposition)
  let subjectEquality :=
    (“&0 = &0” : LO.FirstOrder.ArithmeticProposition)
  let canonicalImplicationResource := branchResource +
    contextualDischargeFullAssemblyCost shiftedGamma
      canonicalBound (Rewriting.free body)
  let canonicalUnderOriginalResource :=
    canonicalImplicationResource +
      weakeningFullAssemblyCost
        (insert canonicalImplication originalContext)
  let originalAssumptionResource :=
    assumptionFullPayloadCost originalContext originalBound
  let backwardResource :=
    (equalitySymmetryImplication
      (iteratedSuccessorTerm 0 bound)
      (Rew.free boundTerm)).payloadLength +
    weakeningFullAssemblyCost
      (insert (forwardEquality 🡒 backwardEquality) shiftedGamma) +
    boundEqualityResource +
    contextualModusPonensFullAssemblyCost shiftedGamma
      forwardEquality backwardEquality
  let backwardUnderOriginalResource :=
    backwardResource +
      weakeningFullAssemblyCost
        (insert backwardEquality originalContext)
  let subjectResource :=
    (proveEqualityReflexivityAtTerm
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).payloadLength +
    weakeningFullAssemblyCost
      (insert subjectEquality originalContext)
  let transportResource :=
    relationTransportImplicationStructuralPayloadBound
      originalContext Language.ORing.Rel.lt
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (Rew.free boundTerm)
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (iteratedSuccessorTerm 0 bound)
      subjectResource backwardUnderOriginalResource
  let canonicalAssumptionResource :=
    transportResource + originalAssumptionResource +
      contextualModusPonensFullAssemblyCost originalContext
        originalBound canonicalBound
  let bodyUnderOriginalResource :=
    canonicalUnderOriginalResource + canonicalAssumptionResource +
      contextualModusPonensFullAssemblyCost originalContext
        canonicalBound (Rewriting.free body)
  let originalImplicationResource :=
    bodyUnderOriginalResource +
      contextualDischargeFullAssemblyCost shiftedGamma
        originalBound (Rewriting.free body)
  originalImplicationResource +
    contextualUniversalIntroductionFullAssemblyCost Gamma
      (termBoundedUniversalBody boundTerm body)

theorem compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (boundEquality : CertifiedPAContextProof
      (Gamma.image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 bound) =
        !!(Rew.free boundTerm)” :
        LO.FirstOrder.ArithmeticProposition))
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound)
    (boundEqualityResource branchResource : Nat)
    (hbound : boundEquality.payloadLength ≤ boundEqualityResource)
    (hbranches :
      branches.compileUnderBoundAssumptionStructuralPayloadBound ≤
        branchResource) :
    compileContextualTermBoundedUniversalStructuralPayloadBound
        bound boundTerm body boundEquality branches ≤
      compileContextualTermBoundedUniversalPayloadEnvelope
        Gamma bound boundTerm body boundEqualityResource branchResource := by
  unfold compileContextualTermBoundedUniversalStructuralPayloadBound
    compileContextualTermBoundedUniversalPayloadEnvelope
    relationTransportImplicationStructuralPayloadBound
  dsimp only
  omega

theorem compileContextualTermBoundedUniversal_payloadLength_le_structural
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (boundEquality : CertifiedPAContextProof
      (Gamma.image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 bound) =
        !!(Rew.free boundTerm)” :
        LO.FirstOrder.ArithmeticProposition))
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound) :
    (compileContextualTermBoundedUniversal
      bound boundTerm body boundEquality branches).payloadLength ≤
      compileContextualTermBoundedUniversalStructuralPayloadBound
        bound boundTerm body boundEquality branches := by
  let shiftedGamma := Gamma.image Rewriting.shift
  let originalBound := freedTermBoundFormula boundTerm
  let canonicalBound := finiteBoundFormula bound
  let originalContext := insert (∼originalBound) shiftedGamma
  let forwardEquality :=
    (“!!(iteratedSuccessorTerm 0 bound) =
      !!(Rew.free boundTerm)” :
      LO.FirstOrder.ArithmeticProposition)
  let backwardEquality :=
    (“!!(Rew.free boundTerm) =
      !!(iteratedSuccessorTerm 0 bound)” :
      LO.FirstOrder.ArithmeticProposition)
  let subjectEquality :=
    (“&0 = &0” : LO.FirstOrder.ArithmeticProposition)
  let underCanonical := branches.compileUnderBoundAssumption
  let canonicalImplication := contextualDischarge
    canonicalBound (Rewriting.free body) underCanonical
  let canonicalImplicationUnderOriginal : CertifiedPAContextProof
      originalContext
      (LO.Arrow.arrow canonicalBound (Rewriting.free body)) :=
    CertifiedPAContextProof.weakenContext canonicalImplication (by
      intro formula hformula
      exact Finset.mem_insert_of_mem hformula)
  let originalAssumption := CertifiedPAContextProof.assumption
    originalContext originalBound (Finset.mem_insert_self _ _)
  let boundBackward := CertifiedPAContextProof.equalitySymmetry
    (iteratedSuccessorTerm 0 bound) (Rew.free boundTerm) boundEquality
  let boundBackwardUnderOriginal : CertifiedPAContextProof originalContext
      backwardEquality :=
    CertifiedPAContextProof.weakenContext boundBackward (by
      intro formula hformula
      exact Finset.mem_insert_of_mem hformula)
  let subjectReflexivity := CertifiedPAContextProof.weakenCertified
    originalContext
    (proveEqualityReflexivityAtTerm
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0))
  let transportRaw := relationTransportImplicationFromEqualities
    Language.ORing.Rel.lt
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (Rew.free boundTerm)
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (iteratedSuccessorTerm 0 bound)
    subjectReflexivity boundBackwardUnderOriginal
  let transport : CertifiedPAContextProof originalContext
      (LO.Arrow.arrow originalBound canonicalBound) := by
    have horiginal := binaryRelationFormula_lt_eq_finiteCaseLessThan
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (Rew.free boundTerm)
    have hcanonical := binaryRelationFormula_lt_eq_finiteCaseLessThan
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (iteratedSuccessorTerm 0 bound)
    have hfinite : finiteCaseLessThanFormula
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
        (iteratedSuccessorTerm 0 bound) = canonicalBound := rfl
    have hformula :
        (LO.Arrow.arrow
          (binaryRelationFormula Language.ORing.Rel.lt
            (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
            (Rew.free boundTerm))
          (binaryRelationFormula Language.ORing.Rel.lt
            (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
            (iteratedSuccessorTerm 0 bound))) =
        LO.Arrow.arrow originalBound canonicalBound := by
      rw [horiginal, hcanonical, hfinite]
      rfl
    exact CertifiedPAContextProof.cast hformula transportRaw
  let canonicalAssumption := CertifiedPAContextProof.modusPonens
    transport originalAssumption
  let bodyUnderOriginal := CertifiedPAContextProof.modusPonens
    canonicalImplicationUnderOriginal canonicalAssumption
  let originalImplication := contextualDischarge
    originalBound (Rewriting.free body) bodyUnderOriginal
  let freeBodyProof : CertifiedPAContextProof shiftedGamma
      (Rewriting.free (termBoundedUniversalBody boundTerm body)) :=
    CertifiedPAContextProof.cast
      (termBoundedUniversalBody_free boundTerm body).symm
      originalImplication

  have hunder : underCanonical.payloadLength ≤
      branches.compileUnderBoundAssumptionStructuralPayloadBound :=
    CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumption_payloadLength_le_structural
      branches
  have hcanonicalRaw := contextualDischarge_payloadLength_le
    canonicalBound (Rewriting.free body) underCanonical
  have hcanonical : canonicalImplication.payloadLength ≤
      branches.compileUnderBoundAssumptionStructuralPayloadBound +
        contextualDischargeFullAssemblyCost shiftedGamma
          canonicalBound (Rewriting.free body) := by
    exact hcanonicalRaw.trans (Nat.add_le_add_right hunder _)
  have hcanonicalWeakRaw :=
    CertifiedPAContextProof.weakenContext_payloadLength_le
      (Delta := originalContext)
      canonicalImplication (by
        intro formula hformula
        exact Finset.mem_insert_of_mem hformula)
  have hcanonicalWeak :
      canonicalImplicationUnderOriginal.payloadLength ≤
        (branches.compileUnderBoundAssumptionStructuralPayloadBound +
          contextualDischargeFullAssemblyCost shiftedGamma
            canonicalBound (Rewriting.free body)) +
        weakeningFullAssemblyCost
          (insert (LO.Arrow.arrow canonicalBound (Rewriting.free body))
            originalContext) := by
    exact hcanonicalWeakRaw.trans (Nat.add_le_add_right hcanonical _)
  have hassumption : originalAssumption.payloadLength =
      assumptionFullPayloadCost originalContext originalBound :=
    assumption_payloadLength_eq _ _ _
  have hbackward := CertifiedPAContextProof.equalitySymmetry_payloadLength_le
    (iteratedSuccessorTerm 0 bound) (Rew.free boundTerm) boundEquality
  have hbackwardWeakRaw :=
    CertifiedPAContextProof.weakenContext_payloadLength_le
      (Delta := originalContext)
      boundBackward (by
        intro formula hformula
        exact Finset.mem_insert_of_mem hformula)
  have hbackwardWeak : boundBackwardUnderOriginal.payloadLength ≤
      ((equalitySymmetryImplication
          (iteratedSuccessorTerm 0 bound)
          (Rew.free boundTerm)).payloadLength +
        weakeningFullAssemblyCost
          (insert (forwardEquality 🡒 backwardEquality) shiftedGamma) +
        boundEquality.payloadLength +
        contextualModusPonensFullAssemblyCost shiftedGamma
          forwardEquality backwardEquality) +
      weakeningFullAssemblyCost
        (insert backwardEquality originalContext) := by
    exact hbackwardWeakRaw.trans (Nat.add_le_add_right hbackward _)
  have hsubject := CertifiedPAContextProof.weakenCertified_payloadLength_le
    originalContext
    (proveEqualityReflexivityAtTerm
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0))
  have htransportRaw :=
    relationTransportImplicationFromEqualities_payloadLength_le
      Language.ORing.Rel.lt
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (Rew.free boundTerm)
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (iteratedSuccessorTerm 0 bound)
      subjectReflexivity boundBackwardUnderOriginal
  have htransportMono :=
    relationTransportImplicationStructuralPayloadBound_mono
      originalContext Language.ORing.Rel.lt
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (Rew.free boundTerm)
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (iteratedSuccessorTerm 0 bound)
      hsubject hbackwardWeak
  have htransport : transport.payloadLength ≤
      relationTransportImplicationStructuralPayloadBound
        originalContext Language.ORing.Rel.lt
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
        (Rew.free boundTerm)
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
        (iteratedSuccessorTerm 0 bound)
        ((proveEqualityReflexivityAtTerm
          (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).payloadLength +
          weakeningFullAssemblyCost
            (insert subjectEquality originalContext))
        (((equalitySymmetryImplication
            (iteratedSuccessorTerm 0 bound)
            (Rew.free boundTerm)).payloadLength +
          weakeningFullAssemblyCost
            (insert (forwardEquality 🡒 backwardEquality) shiftedGamma) +
          boundEquality.payloadLength +
          contextualModusPonensFullAssemblyCost shiftedGamma
            forwardEquality backwardEquality) +
          weakeningFullAssemblyCost
            (insert backwardEquality originalContext)) := by
    have hcast : transport.payloadLength = transportRaw.payloadLength := by
      dsimp only [transport]
      exact CertifiedPAContextProof.cast_payloadLength _ _
    rw [hcast]
    exact htransportRaw.trans htransportMono
  have hcanonicalAssumptionRaw :=
    CertifiedPAContextProof.modusPonens_payloadLength_le
      transport originalAssumption
  change canonicalAssumption.payloadLength ≤
      transport.payloadLength + originalAssumption.payloadLength +
        contextualModusPonensFullAssemblyCost originalContext
          originalBound canonicalBound at hcanonicalAssumptionRaw
  have hbodyRaw := CertifiedPAContextProof.modusPonens_payloadLength_le
    canonicalImplicationUnderOriginal canonicalAssumption
  change bodyUnderOriginal.payloadLength ≤
      canonicalImplicationUnderOriginal.payloadLength +
        canonicalAssumption.payloadLength +
        contextualModusPonensFullAssemblyCost originalContext
          canonicalBound (Rewriting.free body) at hbodyRaw
  have horiginalRaw := contextualDischarge_payloadLength_le
    originalBound (Rewriting.free body) bodyUnderOriginal
  change originalImplication.payloadLength ≤
      bodyUnderOriginal.payloadLength +
        contextualDischargeFullAssemblyCost shiftedGamma
          originalBound (Rewriting.free body) at horiginalRaw
  have hfree : freeBodyProof.payloadLength =
      originalImplication.payloadLength := by
    dsimp only [freeBodyProof]
    exact CertifiedPAContextProof.cast_payloadLength _ _
  have hall := contextualUniversalIntroduction_payloadLength_le
    (termBoundedUniversalBody boundTerm body) freeBodyProof

  change (contextualUniversalIntroduction
      (termBoundedUniversalBody boundTerm body)
      freeBodyProof).payloadLength ≤ _
  rw [compileContextualTermBoundedUniversalStructuralPayloadBound]
  rw [hfree] at hall
  dsimp only [shiftedGamma, originalBound, canonicalBound, originalContext,
    forwardEquality, backwardEquality, subjectEquality] at *
  omega

#print axioms compileContextualTermBoundedUniversal_payloadLength_le_structural
#print axioms
  compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope

end FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
