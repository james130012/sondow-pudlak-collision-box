import integration.FoundationCompactPABoundedUniversalCompiler
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Structural payload bounds for finite PA exhaustion

Every bound in this file is assembled from the public payload theorem of the
actual proof constructor used by the finite-exhaustion route.  No proof length,
proof existence, or semantic completeness premise is accepted as input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteExhaustionBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactCertifiedDisjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPACertifiedInduction
open FoundationCompactPATermSuccessorOrder
open FoundationCompactPALowerBoundSuccessor
open FoundationCompactPAUnaryTermEqualityImplication
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAFiniteCaseAdvance
open FoundationCompactPAFiniteExhaustionBase
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionInduction
open FoundationCompactCertifiedUniversalIntroduction

def addCommutativityStructuralPayloadBound
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  fixedPAPayloadEnvelope +
    specializationCost addCommutativityOuterBody left +
    specializationCost (addCommutativityInnerBody left) right

theorem proveAddCommutativity_payloadLength_le_structural
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddCommutativity left right).payloadLength <=
      addCommutativityStructuralPayloadBound left right := by
  have hproof := proveAddCommutativity_payloadLength_le left right
  have haxiom := addCommutativityAxiomProof_payloadLength_le_fixed
  unfold addCommutativityStructuralPayloadBound
  omega

def addZeroStructuralPayloadBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  fixedPAPayloadEnvelope + specializationCost addZeroBody term

theorem proveAddZeroAtPaZero_payloadLength_le_structural
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddZeroAtPaZero term).payloadLength <=
      addZeroStructuralPayloadBound term := by
  have hproof := proveAddZeroAtPaZero_payloadLength_le term
  have haxiom := addZeroAxiomProof_payloadLength_le_fixed
  unfold addZeroStructuralPayloadBound specializationCost
  omega

def equalityTransitivityStructuralPayloadBound
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftPayloadBound rightPayloadBound : Nat) : Nat :=
  fixedPAPayloadEnvelope +
    specializationCost equalityTransitivityOuterBody left +
    specializationCost (equalityTransitivityMiddleBody left) middle +
    specializationCost (equalityTransitivityInnerBody left middle) right +
    leftPayloadBound + rightPayloadBound + 480 +
    34 * equalityTransitivityFirstMPSyntaxBudget left middle right +
    34 * equalityTransitivitySecondMPSyntaxBudget left middle right

theorem proveEqualityTransitivity_payloadLength_le_structural
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition))
    (leftPayloadBound rightPayloadBound : Nat)
    (hleft : leftProof.payloadLength <= leftPayloadBound)
    (hright : rightProof.payloadLength <= rightPayloadBound) :
    (proveEqualityTransitivity left middle right
      leftProof rightProof).payloadLength <=
      equalityTransitivityStructuralPayloadBound left middle right
        leftPayloadBound rightPayloadBound := by
  have hproof := proveEqualityTransitivity_payloadLength_le
    left middle right leftProof rightProof
  have himplication := equalityTransitivityImplication_payloadLength_le
    left middle right
  have haxiom := equalityTransitivityAxiomProof_payloadLength_le_fixed
  unfold equalityTransitivityStructuralPayloadBound
  omega

def zeroAddTermEqualsTermStructuralPayloadBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  equalityTransitivityStructuralPayloadBound
    (paAddTerm paZeroTerm term)
    (paAddTerm term paZeroTerm) term
    (addCommutativityStructuralPayloadBound paZeroTerm term)
    (addZeroStructuralPayloadBound term)

theorem proveZeroAddTermEqualsTerm_payloadLength_le_structural
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveZeroAddTermEqualsTerm term).payloadLength <=
      zeroAddTermEqualsTermStructuralPayloadBound term := by
  exact proveEqualityTransitivity_payloadLength_le_structural
    (paAddTerm paZeroTerm term)
    (paAddTerm term paZeroTerm) term
    (proveAddCommutativity paZeroTerm term)
    (proveAddZeroAtPaZero term)
    (addCommutativityStructuralPayloadBound paZeroTerm term)
    (addZeroStructuralPayloadBound term)
    (proveAddCommutativity_payloadLength_le_structural paZeroTerm term)
    (proveAddZeroAtPaZero_payloadLength_le_structural term)

def addLtAddStructuralPayloadBound
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadBound : Nat) : Nat :=
  addLtAddImplicationFullPayloadBound left right shift +
    sourcePayloadBound + 240 +
    34 * modusPonensSyntaxBudget
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
      (“!!left + !!shift < !!right + !!shift” :
        LO.FirstOrder.ArithmeticProposition)

theorem proveAddLtAdd_payloadLength_le_structural
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition))
    (sourcePayloadBound : Nat)
    (hsource : sourceProof.payloadLength <= sourcePayloadBound) :
    (proveAddLtAdd left right shift sourceProof).payloadLength <=
      addLtAddStructuralPayloadBound left right shift sourcePayloadBound := by
  have hproof := proveAddLtAdd_payloadLength_le
    left right shift sourceProof
  have himplication := addLtAddImplication_full_payloadLength_le
    left right shift
  unfold addLtAddStructuralPayloadBound
  omega

def shiftedZeroOneStructuralPayloadBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  addLtAddStructuralPayloadBound paZeroTerm paOneTerm term
    (32 + 10 * axiomSyntaxBudget .zeroLtOne)

theorem shiftedZeroOne_payloadLength_le_structural
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddLtAdd paZeroTerm paOneTerm term proveZeroLtOne).payloadLength <=
      shiftedZeroOneStructuralPayloadBound term := by
  exact proveAddLtAdd_payloadLength_le_structural
    paZeroTerm paOneTerm term proveZeroLtOne
    (32 + 10 * axiomSyntaxBudget .zeroLtOne)
    proveZeroLtOne_payloadLength_le

def ltTransportStructuralPayloadBound
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEqualityBound secondEqualityBound relationBound : Nat) : Nat :=
  binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
    leftFirst leftSecond rightFirst rightSecond
    firstEqualityBound secondEqualityBound + relationBound + 240 +
    34 * modusPonensSyntaxBudget
      (“!!leftFirst < !!leftSecond” :
        LO.FirstOrder.ArithmeticProposition)
      (“!!rightFirst < !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)

theorem proveLtTransport_payloadLength_le_structural
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEquality : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondEquality : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition))
    (relationProof : CertifiedPAProof
      (“!!leftFirst < !!leftSecond” :
        LO.FirstOrder.ArithmeticProposition))
    (firstEqualityBound secondEqualityBound relationBound : Nat)
    (hfirst : firstEquality.payloadLength <= firstEqualityBound)
    (hsecond : secondEquality.payloadLength <= secondEqualityBound)
    (hrelation : relationProof.payloadLength <= relationBound) :
    (proveLtTransport leftFirst leftSecond rightFirst rightSecond
      firstEquality secondEquality relationProof).payloadLength <=
      ltTransportStructuralPayloadBound leftFirst leftSecond
        rightFirst rightSecond firstEqualityBound secondEqualityBound
        relationBound := by
  have hproof := proveLtTransport_payloadLength_le
    leftFirst leftSecond rightFirst rightSecond
    firstEquality secondEquality relationProof
  unfold ltTransportStructuralPayloadBound
  unfold binaryRelationTransportFullPayloadBound at hproof ⊢
  omega

def termLtSuccessorStructuralPayloadBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  ltTransportStructuralPayloadBound
    (paAddTerm paZeroTerm term)
    (paAddTerm paOneTerm term)
    term (paAddTerm term paOneTerm)
    (zeroAddTermEqualsTermStructuralPayloadBound term)
    (addCommutativityStructuralPayloadBound paOneTerm term)
    (shiftedZeroOneStructuralPayloadBound term)

theorem proveTermLtSuccessor_payloadLength_le_structural
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveTermLtSuccessor term).payloadLength <=
      termLtSuccessorStructuralPayloadBound term := by
  have hraw := proveLtTransport_payloadLength_le_structural
    (paAddTerm paZeroTerm term)
    (paAddTerm paOneTerm term)
    term (paAddTerm term paOneTerm)
    (proveZeroAddTermEqualsTerm term)
    (proveAddCommutativity paOneTerm term)
    (proveAddLtAdd paZeroTerm paOneTerm term proveZeroLtOne)
    (zeroAddTermEqualsTermStructuralPayloadBound term)
    (addCommutativityStructuralPayloadBound paOneTerm term)
    (shiftedZeroOneStructuralPayloadBound term)
    (proveZeroAddTermEqualsTerm_payloadLength_le_structural term)
    (proveAddCommutativity_payloadLength_le_structural paOneTerm term)
    (shiftedZeroOne_payloadLength_le_structural term)
  simpa only [proveTermLtSuccessor, CertifiedPAProof.cast_payloadLength,
    proveTermLtPaSuccessor, termLtSuccessorStructuralPayloadBound] using hraw

def ltTransImplicationStructuralPayloadBound
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  32 + 10 * axiomSyntaxBudget .ltTrans +
    specializationCost ltTransOuterBody left +
    specializationCost (ltTransMiddleBody left) middle +
    specializationCost (ltTransInnerBody left middle) right

theorem ltTransImplication_payloadLength_le_structural
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (ltTransImplication left middle right).payloadLength <=
      ltTransImplicationStructuralPayloadBound left middle right := by
  have hproof := ltTransImplication_payloadLength_le left middle right
  have haxiom := ltTransAxiomProof_payloadLength_le
  unfold ltTransImplicationStructuralPayloadBound
  omega

def successorLessThanImpliesLessThanStructuralPayloadBound
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼successorLessThanFormula term bound}
  let termSuccessor :=
    (“!!term < !!(successorOf term)” :
      LO.FirstOrder.ArithmeticProposition)
  let antecedent := successorLessThanFormula term bound
  let consequent := termLessThanFormula term bound
  let transitivity :=
    ((“!!term < !!(successorOf term)” :
        LO.FirstOrder.ArithmeticProposition) ⋏ antecedent) 🡒 consequent
  let assumptionBound :=
    CertifiedPAContextProof.assumptionFullPayloadCost Gamma antecedent
  let termSuccessorBound := termLtSuccessorStructuralPayloadBound term +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert termSuccessor Gamma)
  let conjunctionBound := termSuccessorBound + assumptionBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma termSuccessor antecedent
  let implicationBound :=
    ltTransImplicationStructuralPayloadBound term (successorOf term) bound +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert transitivity Gamma)
  implicationBound + conjunctionBound +
    FoundationCompactCertifiedContextualModusPonens.contextualModusPonensFullAssemblyCost
      Gamma (termSuccessor ⋏ antecedent) consequent +
    CertifiedPAContextProof.dischargeFullAssemblyCost antecedent consequent

theorem proveSuccessorLessThanImpliesLessThan_payloadLength_le_structural
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveSuccessorLessThanImpliesLessThan term bound).payloadLength <=
      successorLessThanImpliesLessThanStructuralPayloadBound term bound := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼successorLessThanFormula term bound}
  let successorAssumption := CertifiedPAContextProof.assumption
    Gamma (successorLessThanFormula term bound) (by simp [Gamma])
  let termSuccessorRaw := proveTermLtSuccessor term
  let termSuccessor : CertifiedPAProof
      (“!!term < !!(successorOf term)” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast
      (finiteCaseSuccessorLessThan_formula term).symm termSuccessorRaw
  let contextualTermSuccessor :=
    CertifiedPAContextProof.weakenCertified Gamma termSuccessor
  let antecedentProof := CertifiedPAContextProof.conjunction
    contextualTermSuccessor successorAssumption
  let implicationProof := CertifiedPAContextProof.weakenCertified Gamma
    (ltTransImplication term (successorOf term) bound)
  let result := CertifiedPAContextProof.modusPonens
    implicationProof antecedentProof
  have hassumption := CertifiedPAContextProof.assumption_payloadLength_eq
    Gamma (successorLessThanFormula term bound) (by simp [Gamma])
  have htermRaw := proveTermLtSuccessor_payloadLength_le_structural term
  have htermCast : termSuccessor.payloadLength =
      termSuccessorRaw.payloadLength := by
    exact CertifiedPAProof.cast_payloadLength _ _
  have htermContext := CertifiedPAContextProof.weakenCertified_payloadLength_le
    Gamma termSuccessor
  have hconjunction := CertifiedPAContextProof.conjunction_payloadLength_le
    contextualTermSuccessor successorAssumption
  have himplicationRaw := ltTransImplication_payloadLength_le_structural
    term (successorOf term) bound
  have himplicationContext :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le Gamma
      (ltTransImplication term (successorOf term) bound)
  have hmodus := CertifiedPAContextProof.modusPonens_payloadLength_le
    implicationProof antecedentProof
  have hdischarge := CertifiedPAContextProof.discharge_payloadLength_le
    (successorLessThanFormula term bound)
    (termLessThanFormula term bound) result
  have hterm : termSuccessor.payloadLength <=
      termLtSuccessorStructuralPayloadBound term := by
    rw [htermCast]
    exact htermRaw
  have htermContextBound : contextualTermSuccessor.payloadLength <=
      termLtSuccessorStructuralPayloadBound term +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert
            (“!!term < !!(successorOf term)” :
              LO.FirstOrder.ArithmeticProposition) Gamma) :=
    htermContext.trans (Nat.add_le_add_right hterm _)
  have himplicationContextBound : implicationProof.payloadLength <=
      ltTransImplicationStructuralPayloadBound
          term (successorOf term) bound +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert
            (((“!!term < !!(successorOf term)” :
                LO.FirstOrder.ArithmeticProposition) ⋏
              (successorLessThanFormula term bound)) 🡒
              termLessThanFormula term bound) Gamma) :=
    himplicationContext.trans
      (Nat.add_le_add_right himplicationRaw _)
  have hantecedentBound : antecedentProof.payloadLength <=
      termLtSuccessorStructuralPayloadBound term +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert
            (“!!term < !!(successorOf term)” :
              LO.FirstOrder.ArithmeticProposition) Gamma) +
        CertifiedPAContextProof.assumptionFullPayloadCost Gamma
          (successorLessThanFormula term bound) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost Gamma
          (“!!term < !!(successorOf term)” :
            LO.FirstOrder.ArithmeticProposition)
          (successorLessThanFormula term bound) := by
    calc
      antecedentProof.payloadLength <=
          contextualTermSuccessor.payloadLength +
            successorAssumption.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost Gamma
              (“!!term < !!(successorOf term)” :
                LO.FirstOrder.ArithmeticProposition)
              (successorLessThanFormula term bound) := hconjunction
      _ <= _ := by rw [hassumption]; omega
  have hresultBound : result.payloadLength <=
      ltTransImplicationStructuralPayloadBound
          term (successorOf term) bound +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert
            (((“!!term < !!(successorOf term)” :
                LO.FirstOrder.ArithmeticProposition) ⋏
              successorLessThanFormula term bound) 🡒
              termLessThanFormula term bound) Gamma) +
        (termLtSuccessorStructuralPayloadBound term +
          FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert
              (“!!term < !!(successorOf term)” :
                LO.FirstOrder.ArithmeticProposition) Gamma) +
          CertifiedPAContextProof.assumptionFullPayloadCost Gamma
            (successorLessThanFormula term bound) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost Gamma
            (“!!term < !!(successorOf term)” :
              LO.FirstOrder.ArithmeticProposition)
            (successorLessThanFormula term bound)) +
        FoundationCompactCertifiedContextualModusPonens.contextualModusPonensFullAssemblyCost
          Gamma
          ((“!!term < !!(successorOf term)” :
              LO.FirstOrder.ArithmeticProposition) ⋏
            successorLessThanFormula term bound)
          (termLessThanFormula term bound) := by
    apply hmodus.trans
    simp only [successorLessThanFormula, termLessThanFormula] at *
    omega
  have hfinal := hdischarge.trans
    (Nat.add_le_add_right hresultBound
      (CertifiedPAContextProof.dischargeFullAssemblyCost
        (successorLessThanFormula term bound)
        (termLessThanFormula term bound)))
  change (CertifiedPAContextProof.discharge
    (successorLessThanFormula term bound)
    (termLessThanFormula term bound) result).payloadLength <= _
  simpa [successorLessThanImpliesLessThanStructuralPayloadBound,
    Gamma] using hfinal

def liftLowerBoundThroughSuccessorStructuralPayloadBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (lowerPayloadBound : Nat) : Nat :=
  successorLessThanImpliesLessThanStructuralPayloadBound term bound +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert
        (successorLessThanFormula term bound 🡒
          termLessThanFormula term bound) Gamma) +
    lowerPayloadBound +
    CertifiedPAContextProof.modusTollensFullAssemblyCost Gamma
      (successorLessThanFormula term bound)
      (termLessThanFormula term bound)

theorem liftLowerBoundThroughSuccessor_payloadLength_le_structural
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (lowerBoundProof : CertifiedPAContextProof Gamma
      (∼termLessThanFormula term bound))
    (lowerPayloadBound : Nat)
    (hlower : lowerBoundProof.payloadLength <= lowerPayloadBound) :
    (liftLowerBoundThroughSuccessor term bound
      lowerBoundProof).payloadLength <=
      liftLowerBoundThroughSuccessorStructuralPayloadBound
        Gamma term bound lowerPayloadBound := by
  let implication := proveSuccessorLessThanImpliesLessThan term bound
  let contextualImplication :=
    CertifiedPAContextProof.weakenCertified Gamma implication
  have himplication :=
    proveSuccessorLessThanImpliesLessThan_payloadLength_le_structural
      term bound
  have hweakening := CertifiedPAContextProof.weakenCertified_payloadLength_le
    Gamma implication
  have htollens := CertifiedPAContextProof.modusTollens_payloadLength_le
    contextualImplication lowerBoundProof
  have himplicationBound : implication.payloadLength <=
      successorLessThanImpliesLessThanStructuralPayloadBound term bound := by
    simpa only [implication] using himplication
  have hcontextualBound : contextualImplication.payloadLength <=
      successorLessThanImpliesLessThanStructuralPayloadBound term bound +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert
            (successorLessThanFormula term bound 🡒
              termLessThanFormula term bound) Gamma) := by
    have hraw := hweakening.trans
      (Nat.add_le_add_right himplicationBound _)
    simpa only [contextualImplication] using hraw
  change (CertifiedPAContextProof.modusTollens
    contextualImplication lowerBoundProof).payloadLength <= _
  unfold liftLowerBoundThroughSuccessorStructuralPayloadBound
  calc
    (CertifiedPAContextProof.modusTollens
      contextualImplication lowerBoundProof).payloadLength <=
        contextualImplication.payloadLength +
          lowerBoundProof.payloadLength +
          CertifiedPAContextProof.modusTollensFullAssemblyCost Gamma
            (successorLessThanFormula term bound)
            (termLessThanFormula term bound) := htollens
    _ <= _ := by omega

def successorEqualityUnderCaseStructuralPayloadBound
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  unaryTermEqualityUnderAssumptionStructuralPayloadBound
    unarySuccessorTerm (iteratedSuccessorTerm 0 index) subject

theorem proveSuccessorEqualityUnderCase_payloadLength_le_structural
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveSuccessorEqualityUnderCase index subject).payloadLength <=
      successorEqualityUnderCaseStructuralPayloadBound index subject := by
  let raw := compileUnaryTermEqualityUnderAssumption
    unarySuccessorTerm (iteratedSuccessorTerm 0 index) subject
  let formulaCasted := CertifiedPAContextProof.cast
    (unarySuccessorEqualityFormula_eq index subject) raw
  let result : CertifiedPAContextProof
      ({∼finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) subject} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 (index + 1))
        (successorOf subject)) :=
    CertifiedPAContextProof.castContext
      (finiteCaseEqualityContext_eq_parameterEqualityContext
        (iteratedSuccessorTerm 0 index) subject).symm
      formulaCasted
  have hraw := compileUnaryTermEqualityUnderAssumption_payloadLength_le
    unarySuccessorTerm (iteratedSuccessorTerm 0 index) subject
  have hpayload : result.payloadLength = raw.payloadLength := by
    calc
      result.payloadLength = formulaCasted.payloadLength :=
        CertifiedPAContextProof.castContext_payloadLength _ _
      _ = raw.payloadLength :=
        CertifiedPAContextProof.cast_payloadLength _ _
  change result.payloadLength <= _
  rw [hpayload]
  exact hraw

def injectEqualityCaseStructuralPayloadBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (index : Nat) :
    (remaining : Nat) →
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) →
    (equalityPayloadBound : Nat) → Nat
  | 0, subject, equalityPayloadBound =>
      equalityPayloadBound +
        CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
          (finiteEqualityCases subject index)
          (finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 index) subject)
  | remaining + 1, subject, equalityPayloadBound =>
      injectEqualityCaseStructuralPayloadBound Gamma index remaining
          subject equalityPayloadBound +
        CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
          (finiteEqualityCases subject (Nat.succ (index + remaining)))
          (finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 (Nat.succ (index + remaining)))
            subject)

theorem injectEqualityCase_payloadLength_le_structural
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (index remaining : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAContextProof Gamma
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 index) subject))
    (equalityPayloadBound : Nat)
    (hequality : equalityProof.payloadLength <= equalityPayloadBound) :
    (injectEqualityCase index remaining subject equalityProof).payloadLength <=
      injectEqualityCaseStructuralPayloadBound Gamma index remaining
        subject equalityPayloadBound := by
  induction remaining with
  | zero =>
      have hconstructor := CertifiedPAContextProof.disjunctionRight_payloadLength_le
        (left := finiteEqualityCases subject index) equalityProof
      have hpayload :
          (injectEqualityCase index 0 subject equalityProof).payloadLength =
            (CertifiedPAContextProof.disjunctionRight
              (left := finiteEqualityCases subject index)
              equalityProof).payloadLength := by
        simp only [injectEqualityCase]
        rfl
      rw [hpayload]
      simpa only [injectEqualityCaseStructuralPayloadBound] using
        hconstructor.trans (by omega)
  | succ remaining ih =>
      let previous := injectEqualityCase index remaining subject equalityProof
      have hconstructor := CertifiedPAContextProof.disjunctionLeft_payloadLength_le
        (right := finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 (Nat.succ (index + remaining))) subject)
        previous
      have hprevious : previous.payloadLength <=
          injectEqualityCaseStructuralPayloadBound Gamma index remaining
            subject equalityPayloadBound := by
        simpa only [previous] using ih
      have hpayload :
          (injectEqualityCase index (remaining + 1)
              subject equalityProof).payloadLength =
            (CertifiedPAContextProof.disjunctionLeft
              (right := finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 (Nat.succ (index + remaining)))
                subject)
              previous).payloadLength := by
        simp only [injectEqualityCase]
        rfl
      rw [hpayload]
      simpa only [injectEqualityCaseStructuralPayloadBound] using
        hconstructor.trans (by omega)

def finalLowerBoundUnderCaseStructuralPayloadBound
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  negativeTransportUnderAssumptionStructuralPayloadBound
    Language.ORing.Rel.lt (finalCaseArguments index)
    (iteratedSuccessorTerm 0 index) subject
    (ltIrreflFullPayloadBound
      (iteratedSuccessorTerm 0 (index + 1)))

theorem proveFinalLowerBoundUnderCase_payloadLength_le_structural
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveFinalLowerBoundUnderCase index subject).payloadLength <=
      finalLowerBoundUnderCaseStructuralPayloadBound index subject := by
  let reflexiveNegative := proveLtIrrefl
    (iteratedSuccessorTerm 0 (index + 1))
  let sourceProof : CertifiedPAProof
      (∼unaryRelationFormula Language.ORing.Rel.lt
        (finalCaseArguments index)
        (iteratedSuccessorTerm 0 index)) :=
    CertifiedPAProof.cast (finalCaseSourceFormula_eq index).symm
      (CertifiedPAProof.cast
        (congrArg
          (fun formula : LO.FirstOrder.ArithmeticProposition => ∼formula)
          (finiteCaseLessThanFormula_eq_operator
            (iteratedSuccessorTerm 0 (index + 1))
            (iteratedSuccessorTerm 0 (index + 1))).symm)
        reflexiveNegative)
  let raw := negativeTransportUnderAssumption Language.ORing.Rel.lt
    (finalCaseArguments index)
    (iteratedSuccessorTerm 0 index) subject sourceProof
  let formulaCasted := CertifiedPAContextProof.cast
    (finalCaseTargetFormula_eq index subject) raw
  let result : CertifiedPAContextProof
      ({∼finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) subject} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (∼finiteCaseLessThanFormula
        (successorOf subject)
        (iteratedSuccessorTerm 0 (index + 1))) :=
    CertifiedPAContextProof.castContext
      (finiteCaseEqualityContext_eq_parameterEqualityContext
        (iteratedSuccessorTerm 0 index) subject).symm
      formulaCasted
  have hreflexive := proveLtIrrefl_payloadLength_le
    (iteratedSuccessorTerm 0 (index + 1))
  have hsource : sourceProof.payloadLength <=
      ltIrreflFullPayloadBound
        (iteratedSuccessorTerm 0 (index + 1)) := by
    simpa only [sourceProof, CertifiedPAProof.cast_payloadLength] using
      hreflexive
  have hraw := negativeTransportUnderAssumption_payloadLength_le
    Language.ORing.Rel.lt (finalCaseArguments index)
    (iteratedSuccessorTerm 0 index) subject sourceProof
  have hmonotone :=
    negativeTransportUnderAssumptionStructuralPayloadBound_mono_source
      Language.ORing.Rel.lt (finalCaseArguments index)
      (iteratedSuccessorTerm 0 index) subject hsource
  have hresult := hraw.trans hmonotone
  have hpayload : result.payloadLength = raw.payloadLength := by
    calc
      result.payloadLength = formulaCasted.payloadLength :=
        CertifiedPAContextProof.castContext_payloadLength _ _
      _ = raw.payloadLength :=
        CertifiedPAContextProof.cast_payloadLength _ _
  change result.payloadLength <= _
  rw [hpayload]
  exact hresult

def finiteCaseZeroEqualityStructuralPayloadBound : Nat :=
  paPrimitiveCostEnvelope
    (binaryTermCode inductionZeroTerm).length

theorem finiteCaseZeroEqualityProof_payloadLength_le_structural :
    finiteCaseZeroEqualityProof.payloadLength <=
      finiteCaseZeroEqualityStructuralPayloadBound := by
  have hraw := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    inductionZeroTerm (binaryTermCode inductionZeroTerm).length (by rfl)
  simpa only [finiteCaseZeroEqualityProof,
    CertifiedPAProof.cast_payloadLength,
    finiteCaseZeroEqualityStructuralPayloadBound] using hraw

def finiteCaseZeroNotLessStructuralPayloadBound : Nat :=
  ltIrreflFullPayloadBound inductionZeroTerm

theorem finiteCaseZeroNotLessProof_payloadLength_le_structural :
    finiteCaseZeroNotLessProof.payloadLength <=
      finiteCaseZeroNotLessStructuralPayloadBound := by
  have hraw := proveLtIrrefl_payloadLength_le inductionZeroTerm
  simpa only [finiteCaseZeroNotLessProof,
    CertifiedPAProof.cast_payloadLength,
    finiteCaseZeroNotLessStructuralPayloadBound] using hraw

noncomputable def injectZeroEqualityCaseStructuralPayloadBound :
    Nat → Nat
  | 0 =>
      finiteCaseZeroEqualityStructuralPayloadBound + 96 +
        8 * disjunctionSyntaxBudget
          (⊥ : LO.FirstOrder.ArithmeticProposition)
          (finiteCaseEqualityFormula (finiteCaseZeroTerm 0)
            inductionZeroTerm)
  | tailLength + 1 =>
      injectZeroEqualityCaseStructuralPayloadBound tailLength + 96 +
        8 * disjunctionSyntaxBudget
          (finiteEqualityCases inductionZeroTerm (tailLength + 1))
          (finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 (tailLength + 1))
            inductionZeroTerm)

theorem injectZeroEqualityCase_payloadLength_le_structural
    (tailLength : Nat) :
    (injectZeroEqualityCase tailLength).payloadLength <=
      injectZeroEqualityCaseStructuralPayloadBound tailLength := by
  induction tailLength with
  | zero =>
      have hconstructor :=
        FoundationCompactCertifiedDisjunction.disjunctionRight_payloadLength_le
          (left := (⊥ : LO.FirstOrder.ArithmeticProposition))
          finiteCaseZeroEqualityProof
      have hpayload : (injectZeroEqualityCase 0).payloadLength =
          (FoundationCompactCertifiedDisjunction.disjunctionRight
            (left := (⊥ : LO.FirstOrder.ArithmeticProposition))
            finiteCaseZeroEqualityProof).payloadLength := by
        simp only [injectZeroEqualityCase]
        rfl
      rw [hpayload]
      simpa only [injectZeroEqualityCaseStructuralPayloadBound] using
        hconstructor.trans (by
          have hsource :=
            finiteCaseZeroEqualityProof_payloadLength_le_structural
          omega)
  | succ tailLength ih =>
      let previous := injectZeroEqualityCase tailLength
      have hconstructor :=
        FoundationCompactCertifiedDisjunction.disjunctionLeft_payloadLength_le
          (right := finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 (tailLength + 1)) inductionZeroTerm)
          previous
      have hprevious : previous.payloadLength <=
          injectZeroEqualityCaseStructuralPayloadBound tailLength := by
        simpa only [previous] using ih
      have hpayload :
          (injectZeroEqualityCase (tailLength + 1)).payloadLength =
            (FoundationCompactCertifiedDisjunction.disjunctionLeft
              (right := finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 (tailLength + 1))
                inductionZeroTerm)
              previous).payloadLength := by
        simp only [injectZeroEqualityCase]
        rfl
      rw [hpayload]
      simpa only [injectZeroEqualityCaseStructuralPayloadBound] using
        hconstructor.trans (by omega)

noncomputable def finiteExhaustionZeroFormulaStructuralPayloadBound :
    Nat → Nat
  | 0 =>
      finiteCaseZeroNotLessStructuralPayloadBound + 96 +
        8 * disjunctionSyntaxBudget
          (⊥ : LO.FirstOrder.ArithmeticProposition)
          (∼finiteCaseLessThanFormula inductionZeroTerm
            (finiteCaseZeroTerm 0))
  | tailLength + 1 =>
      injectZeroEqualityCaseStructuralPayloadBound tailLength + 96 +
        8 * disjunctionSyntaxBudget
          (finiteEqualityCases inductionZeroTerm (tailLength + 1))
          (∼finiteCaseLessThanFormula inductionZeroTerm
            (iteratedSuccessorTerm 0 (tailLength + 1)))

theorem proveFiniteExhaustionZeroFormula_payloadLength_le_structural
    (bound : Nat) :
    (proveFiniteExhaustionZeroFormula bound).payloadLength <=
      finiteExhaustionZeroFormulaStructuralPayloadBound bound := by
  cases bound with
  | zero =>
      have hconstructor :=
        FoundationCompactCertifiedDisjunction.disjunctionRight_payloadLength_le
          (left := (⊥ : LO.FirstOrder.ArithmeticProposition))
          finiteCaseZeroNotLessProof
      have hpayload :
          (proveFiniteExhaustionZeroFormula 0).payloadLength =
            (FoundationCompactCertifiedDisjunction.disjunctionRight
              (left := (⊥ : LO.FirstOrder.ArithmeticProposition))
              finiteCaseZeroNotLessProof).payloadLength := by
        simp only [proveFiniteExhaustionZeroFormula]
        rfl
      rw [hpayload]
      simpa only [finiteExhaustionZeroFormulaStructuralPayloadBound] using
        hconstructor.trans (by
          have hsource :=
            finiteCaseZeroNotLessProof_payloadLength_le_structural
          omega)
  | succ tailLength =>
      let casesProof := injectZeroEqualityCase tailLength
      have hconstructor :=
        FoundationCompactCertifiedDisjunction.disjunctionLeft_payloadLength_le
          (right := ∼finiteCaseLessThanFormula inductionZeroTerm
            (iteratedSuccessorTerm 0 (tailLength + 1)))
          casesProof
      have hcases := injectZeroEqualityCase_payloadLength_le_structural
        tailLength
      have hcasesProof : casesProof.payloadLength <=
          injectZeroEqualityCaseStructuralPayloadBound tailLength := by
        simpa only [casesProof] using hcases
      have hpayload :
          (proveFiniteExhaustionZeroFormula (tailLength + 1)).payloadLength =
            (FoundationCompactCertifiedDisjunction.disjunctionLeft
              (right := ∼finiteCaseLessThanFormula inductionZeroTerm
                (iteratedSuccessorTerm 0 (tailLength + 1)))
              casesProof).payloadLength := by
        simp only [proveFiniteExhaustionZeroFormula]
        rfl
      rw [hpayload]
      simpa only [finiteExhaustionZeroFormulaStructuralPayloadBound] using
        hconstructor.trans (by omega)

def finiteExhaustionZeroStructuralPayloadBound
    (bound : Nat) : Nat :=
  finiteExhaustionZeroFormulaStructuralPayloadBound bound

theorem proveFiniteExhaustionZero_payloadLength_le_structural
    (bound : Nat) :
    (proveFiniteExhaustionZero bound).payloadLength <=
      finiteExhaustionZeroStructuralPayloadBound bound := by
  have hraw :=
    proveFiniteExhaustionZeroFormula_payloadLength_le_structural bound
  have hpayload : (proveFiniteExhaustionZero bound).payloadLength =
      (proveFiniteExhaustionZeroFormula bound).payloadLength := by
    exact CertifiedPAProof.cast_payloadLength _ _
  rw [hpayload]
  exact hraw

def preserveLowerBoundBranchStructuralPayloadBound
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼finiteLowerBoundFormula bound subject}
  let lowerPayloadBound :=
    CertifiedPAContextProof.assumptionFullPayloadCost Gamma
      (finiteLowerBoundFormula bound subject)
  liftLowerBoundThroughSuccessorStructuralPayloadBound Gamma subject
      (iteratedSuccessorTerm 0 bound) lowerPayloadBound +
    CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
      (finiteEqualityCases (successorOf subject) bound)
      (finiteLowerBoundFormula bound (successorOf subject))

theorem preserveLowerBoundBranch_payloadLength_le_structural
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (preserveLowerBoundBranch bound subject).payloadLength <=
      preserveLowerBoundBranchStructuralPayloadBound bound subject := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼finiteLowerBoundFormula bound subject}
  let lowerRaw := CertifiedPAContextProof.assumption Gamma
    (finiteLowerBoundFormula bound subject) (by simp [Gamma])
  let lowerStandard := CertifiedPAContextProof.cast
    (finiteLowerBoundFormula_eq_standard bound subject) lowerRaw
  let successorStandard := liftLowerBoundThroughSuccessor
    subject (iteratedSuccessorTerm 0 bound) lowerStandard
  let successorFinite := CertifiedPAContextProof.cast
    (finiteSuccessorLowerBoundFormula_eq_standard bound subject).symm
    successorStandard
  let result := CertifiedPAContextProof.disjunctionRight
    (left := finiteEqualityCases (successorOf subject) bound)
    successorFinite
  have hlowerRaw := CertifiedPAContextProof.assumption_payloadLength_eq
    Gamma (finiteLowerBoundFormula bound subject) (by simp [Gamma])
  have hlowerStandard : lowerStandard.payloadLength =
      lowerRaw.payloadLength := CertifiedPAContextProof.cast_payloadLength _ _
  have hlift := liftLowerBoundThroughSuccessor_payloadLength_le_structural
    subject (iteratedSuccessorTerm 0 bound) lowerStandard
      (CertifiedPAContextProof.assumptionFullPayloadCost Gamma
      (finiteLowerBoundFormula bound subject)) (by
        rw [hlowerStandard, hlowerRaw])
  have hliftStandard : successorStandard.payloadLength <=
      liftLowerBoundThroughSuccessorStructuralPayloadBound Gamma subject
        (iteratedSuccessorTerm 0 bound)
        (CertifiedPAContextProof.assumptionFullPayloadCost Gamma
          (finiteLowerBoundFormula bound subject)) := by
    simpa only [successorStandard] using hlift
  have hsuccessorFinite : successorFinite.payloadLength =
      successorStandard.payloadLength :=
    CertifiedPAContextProof.cast_payloadLength _ _
  have hdisjunction :=
    CertifiedPAContextProof.disjunctionRight_payloadLength_le
      (left := finiteEqualityCases (successorOf subject) bound)
      successorFinite
  have hresult : result.payloadLength <=
      liftLowerBoundThroughSuccessorStructuralPayloadBound Gamma subject
          (iteratedSuccessorTerm 0 bound)
          (CertifiedPAContextProof.assumptionFullPayloadCost Gamma
            (finiteLowerBoundFormula bound subject)) +
        CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
          (finiteEqualityCases (successorOf subject) bound)
          (finiteLowerBoundFormula bound (successorOf subject)) := by
    dsimp only [result]
    rw [hsuccessorFinite] at hdisjunction
    exact hdisjunction.trans (by omega)
  change result.payloadLength <= _
  simpa [preserveLowerBoundBranchStructuralPayloadBound, Gamma] using hresult

noncomputable def advanceFiniteCasePrefixStructuralPayloadBound
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Nat → Nat → Nat
  | 0, remainingLength =>
      CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
        (finiteExhaustionFormula remainingLength (successorOf subject))
  | prefixLength + 1, 0 =>
      let target := finiteExhaustionFormula (prefixLength + 1)
        (successorOf subject)
      let equalityFormula := finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 prefixLength) subject
      let equalityContext : Finset LO.FirstOrder.ArithmeticProposition :=
        {∼equalityFormula}
      let leftBound := advanceFiniteCasePrefixStructuralPayloadBound
        subject prefixLength 1
      let rightBound :=
        finalLowerBoundUnderCaseStructuralPayloadBound prefixLength subject +
          CertifiedPAContextProof.disjunctionFullAssemblyCost
            equalityContext
            (finiteEqualityCases (successorOf subject) (prefixLength + 1))
            (∼finiteCaseLessThanFormula (successorOf subject)
              (iteratedSuccessorTerm 0 (prefixLength + 1)))
      leftBound + rightBound +
        CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
          ∅ target (finiteEqualityCases subject prefixLength)
          equalityFormula
  | prefixLength + 1, remainingLength + 1 =>
      let totalBound := (prefixLength + 1) + (remainingLength + 1)
      let target := finiteExhaustionFormula totalBound
        (successorOf subject)
      let equalityFormula := finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 prefixLength) subject
      let equalityContext : Finset LO.FirstOrder.ArithmeticProposition :=
        {∼equalityFormula}
      let leftBound := advanceFiniteCasePrefixStructuralPayloadBound
        subject prefixLength (remainingLength + 2)
      let nextEqualityBound :=
        successorEqualityUnderCaseStructuralPayloadBound prefixLength subject
      let casesBound := injectEqualityCaseStructuralPayloadBound
        equalityContext (prefixLength + 1) remainingLength
        (successorOf subject) nextEqualityBound
      let rightBound := casesBound +
        CertifiedPAContextProof.disjunctionFullAssemblyCost
          equalityContext
          (finiteEqualityCases (successorOf subject) totalBound)
          (∼finiteCaseLessThanFormula (successorOf subject)
            (iteratedSuccessorTerm 0 totalBound))
      leftBound + rightBound +
        CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
          ∅ target (finiteEqualityCases subject prefixLength)
          equalityFormula
termination_by prefixLength _ => prefixLength

theorem advanceFiniteCasePrefix_payloadLength_le_structural
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (prefixLength remainingLength : Nat) :
    (advanceFiniteCasePrefix subject prefixLength remainingLength).payloadLength <=
      advanceFiniteCasePrefixStructuralPayloadBound
        subject prefixLength remainingLength := by
  induction prefixLength generalizing remainingLength with
  | zero =>
      have hbase := CertifiedPAContextProof.exFalsoAssumption_payloadLength_eq
        (finiteExhaustionFormula remainingLength (successorOf subject))
      have hpayload :
          (advanceFiniteCasePrefix subject 0 remainingLength).payloadLength =
            (CertifiedPAContextProof.exFalsoAssumption
              (finiteExhaustionFormula remainingLength
                (successorOf subject))).payloadLength := by
        simp only [advanceFiniteCasePrefix]
        rw [CertifiedPAContextProof.castContext_payloadLength]
        rw [CertifiedPAContextProof.cast_payloadLength]
      rw [hpayload, hbase]
      simp only [advanceFiniteCasePrefixStructuralPayloadBound]
      exact le_rfl
  | succ prefixLength ih =>
      cases remainingLength with
      | zero =>
          let leftBranch := advanceFiniteCasePrefix subject prefixLength 1
          let lowerProof := proveFinalLowerBoundUnderCase prefixLength subject
          let rightBranch : CertifiedPAContextProof
              ({∼finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 prefixLength) subject} :
                Finset LO.FirstOrder.ArithmeticProposition)
              (finiteExhaustionFormula (prefixLength + 1)
                (successorOf subject)) := by
            unfold finiteExhaustionFormula
            exact CertifiedPAContextProof.disjunctionRight
              (left := finiteEqualityCases
                (successorOf subject) (prefixLength + 1))
              lowerProof
          let combined :=
            CertifiedPAContextProof.eliminateDisjunctionAssumption
              (Gamma := ∅)
              (target := finiteExhaustionFormula (prefixLength + 1)
                (successorOf subject))
              (left := finiteEqualityCases subject prefixLength)
              (right := finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 prefixLength) subject)
              leftBranch rightBranch
          have hleft := ih 1
          have hleftBranch : leftBranch.payloadLength <=
              advanceFiniteCasePrefixStructuralPayloadBound
                subject prefixLength 1 := by
            simpa only [leftBranch] using hleft
          have hlower :=
            proveFinalLowerBoundUnderCase_payloadLength_le_structural
              prefixLength subject
          have hlowerProof : lowerProof.payloadLength <=
              finalLowerBoundUnderCaseStructuralPayloadBound
                prefixLength subject := by
            simpa only [lowerProof] using hlower
          have hrightConstructor :=
            CertifiedPAContextProof.disjunctionRight_payloadLength_le
              (left := finiteEqualityCases
                (successorOf subject) (prefixLength + 1))
              lowerProof
          have hright : rightBranch.payloadLength <=
              finalLowerBoundUnderCaseStructuralPayloadBound
                  prefixLength subject +
                CertifiedPAContextProof.disjunctionFullAssemblyCost
                  ({∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 prefixLength) subject} :
                    Finset LO.FirstOrder.ArithmeticProposition)
                  (finiteEqualityCases
                    (successorOf subject) (prefixLength + 1))
                  (∼finiteCaseLessThanFormula (successorOf subject)
                    (iteratedSuccessorTerm 0 (prefixLength + 1))) := by
            have hpayload : rightBranch.payloadLength =
                (CertifiedPAContextProof.disjunctionRight
                  (left := finiteEqualityCases
                    (successorOf subject) (prefixLength + 1))
                  lowerProof).payloadLength := by
              simp only [rightBranch]
              rfl
            rw [hpayload]
            exact hrightConstructor.trans
              (Nat.add_le_add_right hlowerProof _)
          have hcombined :=
            CertifiedPAContextProof.eliminateDisjunctionAssumption_payloadLength_le
              (Gamma := ∅)
              (target := finiteExhaustionFormula (prefixLength + 1)
                (successorOf subject))
              (left := finiteEqualityCases subject prefixLength)
              (right := finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 prefixLength) subject)
              leftBranch rightBranch
          have hbound : combined.payloadLength <=
              advanceFiniteCasePrefixStructuralPayloadBound
                subject (prefixLength + 1) 0 := by
            have hcombinedPayload := hcombined
            change combined.payloadLength <= _ at hcombinedPayload
            simp only [advanceFiniteCasePrefixStructuralPayloadBound]
            exact hcombinedPayload.trans
              (Nat.add_le_add_right
                (Nat.add_le_add hleftBranch hright) _)
          have hpayload :
              (advanceFiniteCasePrefix subject (prefixLength + 1) 0).payloadLength =
                combined.payloadLength := by
            have heq := congrArg
              (fun proof => proof.payloadLength)
              (advanceFiniteCasePrefix.eq_2 subject prefixLength)
            rw [CertifiedPAContextProof.castContext_payloadLength] at heq
            simpa only [leftBranch, lowerProof, rightBranch, combined] using heq
          rw [hpayload]
          exact hbound
      | succ remainingLength =>
          let leftRaw := advanceFiniteCasePrefix subject prefixLength
            (remainingLength + 2)
          have htotal : prefixLength + (remainingLength + 2) =
              (prefixLength + 1) + (remainingLength + 1) := by omega
          let leftBranch := CertifiedPAContextProof.cast
            (congrArg
              (fun bound => finiteExhaustionFormula bound
                (successorOf subject)) htotal)
            leftRaw
          let nextEquality := proveSuccessorEqualityUnderCase
            prefixLength subject
          let casesProof := injectEqualityCase (prefixLength + 1)
            remainingLength (successorOf subject) nextEquality
          let rightBranch : CertifiedPAContextProof
              ({∼finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 prefixLength) subject} :
                Finset LO.FirstOrder.ArithmeticProposition)
              (finiteExhaustionFormula
                ((prefixLength + 1) + (remainingLength + 1))
                (successorOf subject)) := by
            unfold finiteExhaustionFormula
            apply CertifiedPAContextProof.disjunctionLeft
              (right := finiteLowerBoundFormula
                ((prefixLength + 1) + (remainingLength + 1))
                (successorOf subject))
            simpa only [Nat.add_succ] using casesProof
          let combined :=
            CertifiedPAContextProof.eliminateDisjunctionAssumption
              (Gamma := ∅)
              (target := finiteExhaustionFormula
                ((prefixLength + 1) + (remainingLength + 1))
                (successorOf subject))
              (left := finiteEqualityCases subject prefixLength)
              (right := finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 prefixLength) subject)
              leftBranch rightBranch
          have hleftRaw := ih (remainingLength + 2)
          have hleft : leftBranch.payloadLength <=
              advanceFiniteCasePrefixStructuralPayloadBound subject
                prefixLength (remainingLength + 2) := by
            rw [CertifiedPAContextProof.cast_payloadLength]
            exact hleftRaw
          have hnext :=
            proveSuccessorEqualityUnderCase_payloadLength_le_structural
              prefixLength subject
          have hcases := injectEqualityCase_payloadLength_le_structural
            (Gamma :=
              ({∼finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 prefixLength) subject} :
                Finset LO.FirstOrder.ArithmeticProposition))
            (prefixLength + 1) remainingLength (successorOf subject)
            nextEquality
            (successorEqualityUnderCaseStructuralPayloadBound
              prefixLength subject) (by
                simpa only [nextEquality] using hnext)
          have hrightConstructor :=
            CertifiedPAContextProof.disjunctionLeft_payloadLength_le
              (right := finiteLowerBoundFormula
                ((prefixLength + 1) + (remainingLength + 1))
                (successorOf subject))
              casesProof
          have hrightConstructorNormalized :
              (CertifiedPAContextProof.disjunctionLeft
                (right := finiteLowerBoundFormula
                  ((prefixLength + 1) + (remainingLength + 1))
                  (successorOf subject))
                casesProof).payloadLength <=
                casesProof.payloadLength +
                  CertifiedPAContextProof.disjunctionFullAssemblyCost
                    ({∼finiteCaseEqualityFormula
                        (iteratedSuccessorTerm 0 prefixLength) subject} :
                      Finset LO.FirstOrder.ArithmeticProposition)
                    (finiteEqualityCases (successorOf subject)
                      ((prefixLength + 1) + (remainingLength + 1)))
                    (∼finiteCaseLessThanFormula (successorOf subject)
                      (iteratedSuccessorTerm 0
                        ((prefixLength + 1) + (remainingLength + 1)))) := by
            simpa only [finiteLowerBoundFormula, Nat.add_succ] using
              hrightConstructor
          have hcasesProof : casesProof.payloadLength <=
              injectEqualityCaseStructuralPayloadBound
                ({∼finiteCaseEqualityFormula
                    (iteratedSuccessorTerm 0 prefixLength) subject} :
                  Finset LO.FirstOrder.ArithmeticProposition)
                (prefixLength + 1) remainingLength (successorOf subject)
                (successorEqualityUnderCaseStructuralPayloadBound
                  prefixLength subject) := by
            simpa only [casesProof] using hcases
          have hright : rightBranch.payloadLength <=
              injectEqualityCaseStructuralPayloadBound
                  ({∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 prefixLength) subject} :
                    Finset LO.FirstOrder.ArithmeticProposition)
                  (prefixLength + 1) remainingLength (successorOf subject)
                  (successorEqualityUnderCaseStructuralPayloadBound
                    prefixLength subject) +
                CertifiedPAContextProof.disjunctionFullAssemblyCost
                  ({∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 prefixLength) subject} :
                    Finset LO.FirstOrder.ArithmeticProposition)
                  (finiteEqualityCases (successorOf subject)
                    ((prefixLength + 1) + (remainingLength + 1)))
                  (∼finiteCaseLessThanFormula (successorOf subject)
                    (iteratedSuccessorTerm 0
                      ((prefixLength + 1) + (remainingLength + 1)))) := by
            have hpayload : rightBranch.payloadLength =
                (CertifiedPAContextProof.disjunctionLeft
                  (right := finiteLowerBoundFormula
                    ((prefixLength + 1) + (remainingLength + 1))
                    (successorOf subject))
                  casesProof).payloadLength := by
              simp only [rightBranch]
              rfl
            rw [hpayload]
            exact hrightConstructorNormalized.trans
              (Nat.add_le_add_right hcasesProof _)
          have hcombined :=
            CertifiedPAContextProof.eliminateDisjunctionAssumption_payloadLength_le
              (Gamma := ∅)
              (target := finiteExhaustionFormula
                ((prefixLength + 1) + (remainingLength + 1))
                (successorOf subject))
              (left := finiteEqualityCases subject prefixLength)
              (right := finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 prefixLength) subject)
              leftBranch rightBranch
          have hbound : combined.payloadLength <=
              advanceFiniteCasePrefixStructuralPayloadBound subject
                (prefixLength + 1) (remainingLength + 1) := by
            have hcombinedPayload := hcombined
            change combined.payloadLength <= _ at hcombinedPayload
            simp only [advanceFiniteCasePrefixStructuralPayloadBound]
            exact hcombinedPayload.trans
              (Nat.add_le_add_right (Nat.add_le_add hleft hright) _)
          have hpayload :
              (advanceFiniteCasePrefix subject (prefixLength + 1)
                (remainingLength + 1)).payloadLength =
                combined.payloadLength := by
            have heq := congrArg
              (fun proof => proof.payloadLength)
              (advanceFiniteCasePrefix.eq_3 subject prefixLength
                remainingLength)
            rw [CertifiedPAContextProof.castContext_payloadLength] at heq
            simpa only [leftRaw, leftBranch, nextEquality, casesProof,
              rightBranch, combined] using heq
          rw [hpayload]
          exact hbound

def advanceAllFiniteCasesStructuralPayloadBound
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  advanceFiniteCasePrefixStructuralPayloadBound subject bound 0

theorem advanceAllFiniteCases_payloadLength_le_structural
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (advanceAllFiniteCases bound subject).payloadLength <=
      advanceAllFiniteCasesStructuralPayloadBound bound subject := by
  exact advanceFiniteCasePrefix_payloadLength_le_structural subject bound 0

def finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  advanceAllFiniteCasesStructuralPayloadBound bound subject +
    preserveLowerBoundBranchStructuralPayloadBound bound subject +
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        ∅ (finiteExhaustionFormula bound (successorOf subject))
        (finiteEqualityCases subject bound)
        (finiteLowerBoundFormula bound subject)

theorem proveFiniteExhaustionSuccessorUnderAssumption_payloadLength_le_structural
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveFiniteExhaustionSuccessorUnderAssumption bound subject).payloadLength <=
      finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound
        bound subject := by
  have hcases := advanceAllFiniteCases_payloadLength_le_structural
    bound subject
  have hlower := preserveLowerBoundBranch_payloadLength_le_structural
    bound subject
  have hconstructor :=
    CertifiedPAContextProof.eliminateDisjunctionAssumption_payloadLength_le
      (Gamma := ∅)
      (target := finiteExhaustionFormula bound (successorOf subject))
      (left := finiteEqualityCases subject bound)
      (right := finiteLowerBoundFormula bound subject)
      (advanceAllFiniteCases bound subject)
      (preserveLowerBoundBranch bound subject)
  change (proveFiniteExhaustionSuccessorUnderAssumption
    bound subject).payloadLength <= _ at hconstructor
  unfold finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound
  exact hconstructor.trans
    (Nat.add_le_add_right (Nat.add_le_add hcases hlower) _)

def finiteExhaustionSuccessorImplicationStructuralPayloadBound
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound
      bound subject +
    CertifiedPAContextProof.dischargeFullAssemblyCost
      (finiteExhaustionFormula bound subject)
      (finiteExhaustionFormula bound (successorOf subject))

theorem proveFiniteExhaustionSuccessorImplication_payloadLength_le_structural
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveFiniteExhaustionSuccessorImplication bound subject).payloadLength <=
      finiteExhaustionSuccessorImplicationStructuralPayloadBound
        bound subject := by
  have hunder :=
    proveFiniteExhaustionSuccessorUnderAssumption_payloadLength_le_structural
      bound subject
  have hconstructor := CertifiedPAContextProof.discharge_payloadLength_le
    (finiteExhaustionFormula bound subject)
    (finiteExhaustionFormula bound (successorOf subject))
    (proveFiniteExhaustionSuccessorUnderAssumption bound subject)
  exact hconstructor.trans (by
    unfold finiteExhaustionSuccessorImplicationStructuralPayloadBound
    omega)

def finiteExhaustionStepOpenStructuralPayloadBound (bound : Nat) : Nat :=
  finiteExhaustionSuccessorImplicationStructuralPayloadBound bound (&0)

theorem proveFiniteExhaustionStepOpen_payloadLength_le_structural
    (bound : Nat) :
    (proveFiniteExhaustionStepOpen bound).payloadLength <=
      finiteExhaustionStepOpenStructuralPayloadBound bound := by
  simpa only [proveFiniteExhaustionStepOpen,
    CertifiedPAProof.cast_payloadLength,
    finiteExhaustionStepOpenStructuralPayloadBound] using
      (proveFiniteExhaustionSuccessorImplication_payloadLength_le_structural
        bound (&0))

def finiteExhaustionStepStructuralPayloadBound (bound : Nat) : Nat :=
  finiteExhaustionStepOpenStructuralPayloadBound bound +
    universalIntroductionFullAssemblyCost
      (finiteExhaustionStepBody bound)

theorem proveFiniteExhaustionStep_payloadLength_le_structural
    (bound : Nat) :
    (proveFiniteExhaustionStep bound).payloadLength <=
      finiteExhaustionStepStructuralPayloadBound bound := by
  have hopen := proveFiniteExhaustionStepOpen_payloadLength_le_structural bound
  have hconstructor := universalIntroduction_payloadLength_le
    (finiteExhaustionStepBody bound)
    (proveFiniteExhaustionStepOpen bound)
  rw [show (proveFiniteExhaustionStep bound).payloadLength =
      (universalIntroduction (finiteExhaustionStepBody bound)
        (proveFiniteExhaustionStepOpen bound)).payloadLength by
    simp only [proveFiniteExhaustionStep, CertifiedPAProof.cast_payloadLength]]
  exact hconstructor.trans (by
    unfold finiteExhaustionStepStructuralPayloadBound
    omega)

def finiteExhaustionStructuralPayloadBound (bound : Nat) : Nat :=
  inductionStructuralPayloadBound (finiteExhaustionBody bound)
    (finiteExhaustionZeroStructuralPayloadBound bound)
    (finiteExhaustionStepStructuralPayloadBound bound)

theorem proveFiniteExhaustion_payloadLength_le_structural
    (bound : Nat) :
    (proveFiniteExhaustion bound).payloadLength <=
      finiteExhaustionStructuralPayloadBound bound := by
  have hzero := proveFiniteExhaustionZero_payloadLength_le_structural bound
  have hstep := proveFiniteExhaustionStep_payloadLength_le_structural bound
  have hinduction := proveInduction_payloadLength_le_structuralPayloadBound
    (finiteExhaustionBody bound)
    (finiteExhaustionBody_freeVariables_eq_empty bound)
    (proveFiniteExhaustionZero bound)
    (proveFiniteExhaustionStep bound)
  change (proveFiniteExhaustion bound).payloadLength <= _ at hinduction
  exact hinduction.trans (by
    dsimp only [finiteExhaustionStructuralPayloadBound,
      inductionStructuralPayloadBound]
    omega)

#print axioms proveTermLtSuccessor_payloadLength_le_structural
#print axioms proveSuccessorLessThanImpliesLessThan_payloadLength_le_structural
#print axioms liftLowerBoundThroughSuccessor_payloadLength_le_structural
#print axioms proveSuccessorEqualityUnderCase_payloadLength_le_structural
#print axioms injectEqualityCase_payloadLength_le_structural
#print axioms proveFinalLowerBoundUnderCase_payloadLength_le_structural
#print axioms proveFiniteExhaustionZero_payloadLength_le_structural
#print axioms preserveLowerBoundBranch_payloadLength_le_structural
#print axioms advanceFiniteCasePrefix_payloadLength_le_structural
#print axioms proveFiniteExhaustionSuccessorImplication_payloadLength_le_structural
#print axioms proveFiniteExhaustion_payloadLength_le_structural

end FoundationCompactPAFiniteExhaustionBounds
