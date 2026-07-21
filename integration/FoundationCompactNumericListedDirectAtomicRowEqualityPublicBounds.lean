import integration.FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
import integration.FoundationCompactPABitMembershipValuationCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

/-!
# Public structural resources for direct atomic-row equality

The bit-equivalence branch charges both Boolean outcomes, so its resource is
independent of the proof-selected bit value.  The bounded universal then uses
the finite sum of these public branch envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate

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

private theorem paMulTerm_freeVariables
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact binaryFunctionTerm_freeVariables Language.Mul.mul left right

/-- A proof-free envelope for either Boolean branch of one row-bit equality. -/
def atomicRowEqBitBranchPublicPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm := atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
  let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
  let otherFalse := binaryBitAtValuationFormula false otherIndexTerm valueTerm
  let forward := (∼leftAtom ⋎ otherAtom)
  let backward := (∼otherAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let leftTrueContext := valuationContext leftTrue.freeVariables branchValuation
  let leftFalseContext := valuationContext leftFalse.freeVariables branchValuation
  let otherTrueContext := valuationContext otherTrue.freeVariables branchValuation
  let otherFalseContext := valuationContext otherFalse.freeVariables branchValuation
  let forwardContext := valuationContext forward.freeVariables branchValuation
  let backwardContext := valuationContext backward.freeVariables branchValuation
  let targetContext := valuationContext target.freeVariables branchValuation
  compileBinaryBitLiteralAtValuationPayloadPolynomial true branchValuation
      leftIndexTerm valueTerm +
    compileBinaryBitLiteralAtValuationPayloadPolynomial false branchValuation
      leftIndexTerm valueTerm +
    compileBinaryBitLiteralAtValuationPayloadPolynomial true branchValuation
      otherIndexTerm valueTerm +
    compileBinaryBitLiteralAtValuationPayloadPolynomial false branchValuation
      otherIndexTerm valueTerm +
    weakeningFullAssemblyCost (insert leftTrue leftTrueContext) +
    weakeningFullAssemblyCost (insert leftFalse leftFalseContext) +
    weakeningFullAssemblyCost (insert otherTrue otherTrueContext) +
    weakeningFullAssemblyCost (insert otherFalse otherFalseContext) +
    weakeningFullAssemblyCost (insert leftFalse forwardContext) +
    weakeningFullAssemblyCost (insert otherTrue forwardContext) +
    weakeningFullAssemblyCost (insert otherFalse backwardContext) +
    weakeningFullAssemblyCost (insert leftTrue backwardContext) +
    disjunctionFullAssemblyCost forwardContext (∼leftAtom) otherAtom +
    disjunctionFullAssemblyCost backwardContext (∼otherAtom) leftAtom +
    weakeningFullAssemblyCost (insert forward targetContext) +
    weakeningFullAssemblyCost (insert backward targetContext) +
    conjunctionFullAssemblyCost targetContext forward backward

theorem atomicRowEqBitBranchCertificate_structuralPayloadBound_le_public
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (bitIndex : Nat)
    (hleftCard :
      ((atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hotherCard :
      ((atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hbit : (termValue valuation tokenTableTerm).testBit
        (termValue valuation leftTerm * termValue valuation widthTerm +
          bitIndex) =
      (termValue valuation tokenTableTerm).testBit
        (termValue valuation otherLeftTerm * termValue valuation widthTerm +
          bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (atomicRowEqBitBranchCertificate valuation tokenTableTerm widthTerm
          leftTerm otherLeftTerm bitIndex hbit) <=
      atomicRowEqBitBranchPublicPayloadEnvelope valuation tokenTableTerm
        widthTerm leftTerm otherLeftTerm bitIndex := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm := atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  have hleftTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      true branchValuation leftIndexTerm valueTerm (by
        simpa only [leftIndexTerm, valueTerm] using hleftCard)
  have hleftFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      false branchValuation leftIndexTerm valueTerm (by
        simpa only [leftIndexTerm, valueTerm] using hleftCard)
  have hotherTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      true branchValuation otherIndexTerm valueTerm (by
        simpa only [otherIndexTerm, valueTerm] using hotherCard)
  have hotherFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      false branchValuation otherIndexTerm valueTerm (by
        simpa only [otherIndexTerm, valueTerm] using hotherCard)
  let expected := (termValue valuation tokenTableTerm).testBit
    (termValue valuation leftTerm * termValue valuation widthTerm + bitIndex)
  cases hexpected : expected with
  | false =>
    dsimp only [expected] at hexpected
    simp only [atomicRowEqBitBranchCertificate, hexpected]
    rw [dif_neg (show ¬(false = true) by simp)]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold atomicRowEqBitBranchPublicPayloadEnvelope
    dsimp only [branchValuation, leftIndexTerm, otherIndexTerm, valueTerm] at *
    simp only [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
      Bool.false_eq_true, ↓reduceIte] at *
    omega
  | true =>
    dsimp only [expected] at hexpected
    simp only [atomicRowEqBitBranchCertificate, hexpected]
    rw [dif_pos (show True by trivial)]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold atomicRowEqBitBranchPublicPayloadEnvelope
    dsimp only [branchValuation, leftIndexTerm, otherIndexTerm, valueTerm] at *
    simp only [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
      Bool.false_eq_true, ↓reduceIte] at *
    omega

noncomputable def atomicRowEqBitBranchPublicPayloadSum
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm) : Nat :=
  ∑ bitIndex : Fin (termValue valuation widthTerm),
    atomicRowEqBitBranchPublicPayloadEnvelope valuation tokenTableTerm
      widthTerm leftTerm otherLeftTerm bitIndex

theorem atomicRowEqDirectHybridBranches_leafPayloadBound_public
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (hleftCard :
      ((atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hotherCard :
      ((atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          (termValue valuation leftTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          (termValue valuation otherLeftTerm * termValue valuation widthTerm +
            bitIndex)) :
    HybridBranchesLeafPayloadBound
      (atomicRowEqBitBranchPublicPayloadSum valuation tokenTableTerm widthTerm
        leftTerm otherLeftTerm)
      (atomicRowEqDirectHybridBranches valuation tokenTableTerm widthTerm
        leftTerm otherLeftTerm hbits) := by
  unfold atomicRowEqDirectHybridBranches
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro bitIndex hbitIndex
  let finiteIndex : Fin (termValue valuation widthTerm) :=
    ⟨bitIndex, hbitIndex⟩
  have hbranch :=
    atomicRowEqBitBranchCertificate_structuralPayloadBound_le_public
      valuation tokenTableTerm widthTerm leftTerm otherLeftTerm bitIndex
      hleftCard hotherCard (hbits bitIndex hbitIndex)
  have hsum :
      atomicRowEqBitBranchPublicPayloadEnvelope valuation tokenTableTerm
          widthTerm leftTerm otherLeftTerm finiteIndex <=
        atomicRowEqBitBranchPublicPayloadSum valuation tokenTableTerm
          widthTerm leftTerm otherLeftTerm := by
    unfold atomicRowEqBitBranchPublicPayloadSum
    exact Finset.single_le_sum
      (fun (candidate : Fin (termValue valuation widthTerm)) _ =>
        Nat.zero_le
          (atomicRowEqBitBranchPublicPayloadEnvelope valuation tokenTableTerm
            widthTerm leftTerm otherLeftTerm candidate))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hbranch hsum ⊢
  exact hbranch.trans hsum

noncomputable def atomicRowEqBranchesTransparentStructuralEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm) : Nat :=
  let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue valuation widthTerm
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    valuation body
    (atomicRowEqBitBranchPublicPayloadSum valuation tokenTableTerm widthTerm
      leftTerm otherLeftTerm)
    bound

theorem atomicRowEqBranchesStructuralPayloadEnvelope_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (hleftCard :
      ((atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hotherCard :
      ((atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          (termValue valuation leftTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          (termValue valuation otherLeftTerm * termValue valuation widthTerm +
            bitIndex)) :
    let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift widthTerm) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue valuation widthTerm) outerFormula.freeVariables
        (atomicRowEqDirectHybridBranches valuation tokenTableTerm widthTerm
          leftTerm otherLeftTerm hbits) <=
      atomicRowEqBranchesTransparentStructuralEnvelope valuation
        tokenTableTerm widthTerm leftTerm otherLeftTerm := by
  let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue valuation widthTerm
  let branches := atomicRowEqDirectHybridBranches valuation tokenTableTerm
    widthTerm leftTerm otherLeftTerm hbits
  have hleaves := atomicRowEqDirectHybridBranches_leafPayloadBound_public
    valuation tokenTableTerm widthTerm leftTerm otherLeftTerm
    hleftCard hotherCard hbits
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (atomicRowEqBitBranchPublicPayloadSum valuation tokenTableTerm widthTerm
      leftTerm otherLeftTerm)
    branches hleaves
  simpa only [atomicRowEqBranchesTransparentStructuralEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def atomicRowEqUniversalStructuralPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm) : Nat :=
  let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (atomicRowEqBranchesTransparentStructuralEnvelope valuation tokenTableTerm
      widthTerm leftTerm otherLeftTerm)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift widthTerm) body
    (compileShiftedBoundEqualityPayloadResource valuation outerVariables
      widthTerm)
    branchResource

theorem atomicRowEqUniversalCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (hleftCard :
      ((atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hotherCard :
      ((atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          (termValue valuation leftTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          (termValue valuation otherLeftTerm * termValue valuation widthTerm +
            bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (atomicRowEqUniversalCertificate valuation tokenTableTerm widthTerm
          leftTerm otherLeftTerm hbits) <=
      atomicRowEqUniversalStructuralPayloadEnvelope valuation tokenTableTerm
        widthTerm leftTerm otherLeftTerm := by
  let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branches := atomicRowEqDirectHybridBranches valuation tokenTableTerm
    widthTerm leftTerm otherLeftTerm hbits
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore := atomicRowEqBranchesTransparentStructuralEnvelope
    valuation tokenTableTerm widthTerm leftTerm otherLeftTerm
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource valuation
    outerVariables widthTerm
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body]
    exact atomicRowEqBranchesStructuralPayloadEnvelope_le_transparent
      valuation tokenTableTerm widthTerm leftTerm otherLeftTerm
      hleftCard hotherCard hbits
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift widthTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [atomicRowEqUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    atomicRowEqUniversalStructuralPayloadEnvelope,
    body, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

def atomicRowEqStrictStructuralPayloadResource
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
    ![leftTerm, rightTerm]

theorem strictCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hstrict : termValue valuation leftTerm < termValue valuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (strictCertificate valuation leftTerm rightTerm hstrict) <=
      atomicRowEqStrictStructuralPayloadResource valuation leftTerm rightTerm := by
  simp only [strictCertificate, hybridFormulaStructuralPayloadBound,
    atomicRowEqStrictStructuralPayloadResource]
  exact le_rfl

def atomicRowEqSuccessorStructuralPayloadResource
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource valuation Language.Eq.eq
    ![rightTerm, (‘!!leftTerm + 1’ : ValuationTerm)]

theorem successorCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hsuccessor :
      termValue valuation rightTerm = termValue valuation leftTerm + 1) :
    hybridFormulaStructuralPayloadBound
        (successorCertificate valuation leftTerm rightTerm hsuccessor) <=
      atomicRowEqSuccessorStructuralPayloadResource valuation leftTerm
        rightTerm := by
  simp only [successorCertificate, hybridFormulaStructuralPayloadBound,
    atomicRowEqSuccessorStructuralPayloadResource]
  exact le_rfl

noncomputable def compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm) : Nat :=
  let leftStrictFormula : ValuationFormula :=
    “!!leftTerm < !!tokenCountTerm”
  let leftSuccessorFormula : ValuationFormula :=
    “!!rightTerm = !!leftTerm + 1”
  let otherStrictFormula : ValuationFormula :=
    “!!otherLeftTerm < !!tokenCountTerm”
  let otherSuccessorFormula : ValuationFormula :=
    “!!otherRightTerm = !!otherLeftTerm + 1”
  let universalFormula : ValuationFormula :=
    (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
      otherLeftTerm).ballLT widthTerm
  let leftStrictResource := atomicRowEqStrictStructuralPayloadResource
    valuation leftTerm tokenCountTerm
  let leftSuccessorResource := atomicRowEqSuccessorStructuralPayloadResource
    valuation leftTerm rightTerm
  let otherStrictResource := atomicRowEqStrictStructuralPayloadResource
    valuation otherLeftTerm tokenCountTerm
  let otherSuccessorResource := atomicRowEqSuccessorStructuralPayloadResource
    valuation otherLeftTerm otherRightTerm
  let universalResource := atomicRowEqUniversalStructuralPayloadEnvelope
    valuation tokenTableTerm widthTerm leftTerm otherLeftTerm
  let otherSuccessorUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope valuation
      otherSuccessorFormula universalFormula otherSuccessorResource
      universalResource
  let otherStrictTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation otherStrictFormula
      (otherSuccessorFormula ⋏ universalFormula)
    otherStrictResource otherSuccessorUniversalResource
  let leftSuccessorTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation leftSuccessorFormula
      (otherStrictFormula ⋏ (otherSuccessorFormula ⋏ universalFormula))
    leftSuccessorResource otherStrictTailResource
  transparentHybridConjunctionPayloadEnvelope valuation leftStrictFormula
    (leftSuccessorFormula ⋏
      (otherStrictFormula ⋏ (otherSuccessorFormula ⋏ universalFormula)))
    leftStrictResource leftSuccessorTailResource

theorem atomicRowEqBitTermUnionCards_le_four_of_closed
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (htable : tokenTableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hleft : leftTerm.freeVariables = ∅)
    (hother : otherLeftTerm.freeVariables = ∅) :
    ((atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ∪
          (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4 ∧
      ((atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm).freeVariables ∪
          (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4 := by
  have hleftSubset :
      (atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ∪
          (atomicRowEqBitValueTerm tokenTableTerm).freeVariables ⊆ {0} := by
    have hmul : (paMulTerm leftTerm widthTerm).freeVariables = ∅ := by
      rw [paMulTerm_freeVariables, hleft, hwidth]
      simp
    have hshiftMul := shiftedTerm_freeVariables_eq_empty_of_closed
      (paMulTerm leftTerm widthTerm) hmul
    have hshiftTable := shiftedTerm_freeVariables_eq_empty_of_closed
      tokenTableTerm htable
    rw [atomicRowEqLeftBitIndexTerm, atomicRowEqBitValueTerm,
      binaryFunctionTerm_freeVariables, hshiftMul, hshiftTable]
    simp
  have hotherSubset :
      (atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm).freeVariables ∪
          (atomicRowEqBitValueTerm tokenTableTerm).freeVariables ⊆ {0} := by
    have hmul : (paMulTerm otherLeftTerm widthTerm).freeVariables = ∅ := by
      rw [paMulTerm_freeVariables, hother, hwidth]
      simp
    have hshiftMul := shiftedTerm_freeVariables_eq_empty_of_closed
      (paMulTerm otherLeftTerm widthTerm) hmul
    have hshiftTable := shiftedTerm_freeVariables_eq_empty_of_closed
      tokenTableTerm htable
    rw [atomicRowEqOtherLeftBitIndexTerm, atomicRowEqBitValueTerm,
      binaryFunctionTerm_freeVariables, hshiftMul, hshiftTable]
    simp
  constructor
  · exact (Finset.card_le_card hleftSubset).trans (by simp)
  · exact (Finset.card_le_card hotherSubset).trans (by simp)

theorem
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm)
    (hleftCard :
      ((atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hotherCard :
      ((atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm).freeVariables ∪
        (atomicRowEqBitValueTerm tokenTableTerm).freeVariables).card <= 4)
    (hgraph : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm)
      (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm)
      (termValue valuation leftTerm)
      (termValue valuation rightTerm)
      (termValue valuation otherLeftTerm)
      (termValue valuation otherRightTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
          valuation tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm
          otherLeftTerm otherRightTerm hgraph) <=
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
        otherRightTerm := by
  let leftStrictCertificate := strictCertificate valuation leftTerm
    tokenCountTerm hgraph.1
  let leftSuccessorCertificate := successorCertificate valuation leftTerm
    rightTerm hgraph.2.1
  let otherStrictCertificate := strictCertificate valuation otherLeftTerm
    tokenCountTerm hgraph.2.2.1
  let otherSuccessorCertificate := successorCertificate valuation otherLeftTerm
    otherRightTerm hgraph.2.2.2.1
  let universalCertificate := atomicRowEqUniversalCertificate valuation
    tokenTableTerm widthTerm leftTerm otherLeftTerm hgraph.2.2.2.2
  have hleftStrict := strictCertificate_structuralPayloadBound_le_transparent
    valuation leftTerm tokenCountTerm hgraph.1
  have hleftSuccessor :=
    successorCertificate_structuralPayloadBound_le_transparent valuation
      leftTerm rightTerm hgraph.2.1
  have hotherStrict := strictCertificate_structuralPayloadBound_le_transparent
    valuation otherLeftTerm tokenCountTerm hgraph.2.2.1
  have hotherSuccessor :=
    successorCertificate_structuralPayloadBound_le_transparent valuation
      otherLeftTerm otherRightTerm hgraph.2.2.2.1
  have huniversal :=
    atomicRowEqUniversalCertificate_structuralPayloadBound_le_transparent
      valuation tokenTableTerm widthTerm leftTerm otherLeftTerm
      hleftCard hotherCard hgraph.2.2.2.2
  let otherSuccessorUniversal :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      otherSuccessorCertificate universalCertificate
  have hotherSuccessorUniversal := transparentHybridConjunctionPayloadBound_le
    otherSuccessorCertificate universalCertificate _ _
    hotherSuccessor huniversal
  let otherStrictTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      otherStrictCertificate otherSuccessorUniversal
  have hotherStrictTail := transparentHybridConjunctionPayloadBound_le
    otherStrictCertificate otherSuccessorUniversal _ _
    hotherStrict hotherSuccessorUniversal
  let leftSuccessorTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftSuccessorCertificate otherStrictTail
  have hleftSuccessorTail := transparentHybridConjunctionPayloadBound_le
    leftSuccessorCertificate otherStrictTail _ _
    hleftSuccessor hotherStrictTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftStrictCertificate leftSuccessorTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    leftStrictCertificate leftSuccessorTail _ _
    hleftStrict hleftSuccessorTail
  unfold compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope
  simpa only [
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    leftStrictCertificate, leftSuccessorCertificate,
    otherStrictCertificate, otherSuccessorCertificate,
    universalCertificate, otherSuccessorUniversal, otherStrictTail,
    leftSuccessorTail, parts,
    atomicRowEqStrictStructuralPayloadResource,
    atomicRowEqSuccessorStructuralPayloadResource] using hparts

theorem
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm)
    (htable : tokenTableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hleft : leftTerm.freeVariables = ∅)
    (hother : otherLeftTerm.freeVariables = ∅)
    (hgraph : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm)
      (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm)
      (termValue valuation leftTerm)
      (termValue valuation rightTerm)
      (termValue valuation otherLeftTerm)
      (termValue valuation otherRightTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
          valuation tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm
          otherLeftTerm otherRightTerm hgraph) <=
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
        otherRightTerm := by
  have hcards := atomicRowEqBitTermUnionCards_le_four_of_closed
    tokenTableTerm widthTerm leftTerm otherLeftTerm
    htable hwidth hleft hother
  exact
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      valuation tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm
      otherLeftTerm otherRightTerm hcards.1 hcards.2 hgraph

#print axioms
  atomicRowEqBitBranchCertificate_structuralPayloadBound_le_public
#print axioms
  atomicRowEqDirectHybridBranches_leafPayloadBound_public
#print axioms
  atomicRowEqUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed

end FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
