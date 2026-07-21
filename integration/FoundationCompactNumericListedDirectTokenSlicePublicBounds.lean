import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for valuation-term token slices

The two bounded universal layers are charged by explicit sums of proof-free
leaf envelopes.  No equality proof supplied by the caller occurs in any
resource definition below.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSlicePublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationTermCompiler

def tokenSliceAtValuationCountGuardStructuralEnvelope
    (valuation : Nat -> Nat) (tokenCountTerm : ValuationTerm)
    (count : Nat) : Nat :=
  compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm count,
      (‘!!tokenCountTerm + 1’ : ValuationTerm)]

theorem tokenSliceAtValuationCountGuardCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (tokenCountTerm : ValuationTerm)
    (count : Nat)
    (hbound : count <= termValue valuation tokenCountTerm) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationCountGuardCertificate valuation tokenCountTerm
          count hbound) <=
      tokenSliceAtValuationCountGuardStructuralEnvelope valuation
        tokenCountTerm count := by
  simp only [tokenSliceAtValuationCountGuardCertificate,
    hybridFormulaStructuralPayloadBound]
  rfl

def tokenSliceAtValuationEndpointStructuralEnvelope
    (valuation : Nat -> Nat) (startTerm finishTerm : ValuationTerm)
    (count : Nat) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘!!startTerm + !!(shortBinaryNumeralTerm count)’
  compilePositiveRelationPayloadResource valuation Language.Eq.eq
    ![finishTerm, rightTerm]

theorem tokenSliceAtValuationEndpointCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (startTerm finishTerm : ValuationTerm)
    (count : Nat)
    (hendpoint : termValue valuation finishTerm =
      termValue valuation startTerm + count) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationEndpointCertificate valuation startTerm
          finishTerm count hendpoint) <=
      tokenSliceAtValuationEndpointStructuralEnvelope valuation startTerm
        finishTerm count := by
  simp only [tokenSliceAtValuationEndpointCertificate,
    hybridFormulaStructuralPayloadBound]
  rfl

def tokenSliceAtValuationLeStructuralEnvelope
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  compilePositiveRelationPayloadResource valuation Language.Eq.eq args +
    compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem tokenSliceAtValuationLeCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hle : termValue valuation leftTerm <= termValue valuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationLeCertificate valuation leftTerm rightTerm hle) <=
      tokenSliceAtValuationLeStructuralEnvelope valuation leftTerm
        rightTerm := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  by_cases hequal : termValue valuation leftTerm =
      termValue valuation rightTerm
  · simp only [tokenSliceAtValuationLeCertificate]
    rw [dif_pos hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold tokenSliceAtValuationLeStructuralEnvelope
    dsimp only [args]
    omega
  · simp only [tokenSliceAtValuationLeCertificate]
    rw [dif_neg hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold tokenSliceAtValuationLeStructuralEnvelope
    dsimp only [args]
    omega

def tokenSliceAtValuationBitAtomStructuralEnvelope
    (expected : Bool) (valuation : Nat -> Nat)
    (tokenTableTerm startTerm widthTerm : ValuationTerm)
    (offset bitIndex : Nat) : Nat :=
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tokenTableTerm)
  let formula := binaryBitAtValuationFormula expected indexTerm valueTerm
  let Gamma := valuationContext formula.freeVariables branchValuation
  compileBinaryBitLiteralAtValuationPayloadResource expected branchValuation
      indexTerm valueTerm +
    weakeningFullAssemblyCost (insert formula Gamma)

theorem tokenSliceAtValuationBitAtomTrueCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm startTerm widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hbit : (termValue valuation tokenTableTerm).testBit
      ((termValue valuation startTerm + offset) *
        termValue valuation widthTerm + bitIndex) = true) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationBitAtomTrueCertificate valuation tokenTableTerm
          startTerm widthTerm offset bitIndex hbit) <=
      tokenSliceAtValuationBitAtomStructuralEnvelope true valuation
        tokenTableTerm startTerm widthTerm offset bitIndex := by
  simp only [tokenSliceAtValuationBitAtomTrueCertificate,
    hybridFormulaStructuralPayloadBound,
    tokenSliceAtValuationBitAtomStructuralEnvelope]
  exact le_rfl

theorem tokenSliceAtValuationBitAtomFalseCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm startTerm widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hbit : (termValue valuation tokenTableTerm).testBit
      ((termValue valuation startTerm + offset) *
        termValue valuation widthTerm + bitIndex) = false) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationBitAtomFalseCertificate valuation tokenTableTerm
          startTerm widthTerm offset bitIndex hbit) <=
      tokenSliceAtValuationBitAtomStructuralEnvelope false valuation
        tokenTableTerm startTerm widthTerm offset bitIndex := by
  simp only [tokenSliceAtValuationBitAtomFalseCertificate,
    hybridFormulaStructuralPayloadBound,
    tokenSliceAtValuationBitAtomStructuralEnvelope]
  exact le_rfl

def tokenSliceAtValuationBitFalseBranchStructuralEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat) : Nat :=
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let sourceAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    sourceStartTerm widthTerm
  let targetAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    targetStartTerm widthTerm
  let sourceResource := tokenSliceAtValuationBitAtomStructuralEnvelope false
    valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
  let targetResource := tokenSliceAtValuationBitAtomStructuralEnvelope false
    valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
  let forwardResource := transparentHybridDisjunctionLeftPayloadEnvelope
    branchValuation (∼sourceAtom) targetAtom sourceResource
  let backwardResource := transparentHybridDisjunctionLeftPayloadEnvelope
    branchValuation (∼targetAtom) sourceAtom targetResource
  transparentHybridConjunctionPayloadEnvelope branchValuation
    (∼sourceAtom ⋎ targetAtom) (∼targetAtom ⋎ sourceAtom)
    forwardResource backwardResource

def tokenSliceAtValuationBitTrueBranchStructuralEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat) : Nat :=
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let sourceAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    sourceStartTerm widthTerm
  let targetAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    targetStartTerm widthTerm
  let sourceResource := tokenSliceAtValuationBitAtomStructuralEnvelope true
    valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
  let targetResource := tokenSliceAtValuationBitAtomStructuralEnvelope true
    valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
  let forwardResource := transparentHybridDisjunctionRightPayloadEnvelope
    branchValuation (∼sourceAtom) targetAtom targetResource
  let backwardResource := transparentHybridDisjunctionRightPayloadEnvelope
    branchValuation (∼targetAtom) sourceAtom sourceResource
  transparentHybridConjunctionPayloadEnvelope branchValuation
    (∼sourceAtom ⋎ targetAtom) (∼targetAtom ⋎ sourceAtom)
    forwardResource backwardResource

def tokenSliceAtValuationBitBranchStructuralEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat) : Nat :=
  tokenSliceAtValuationBitFalseBranchStructuralEnvelope valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset bitIndex +
    tokenSliceAtValuationBitTrueBranchStructuralEnvelope valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset bitIndex

theorem tokenSliceAtValuationBitBranchCertificateFromData_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat)
    (data : TokenSliceAtValuationBitBranchData valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset bitIndex) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationBitBranchCertificateFromData valuation
          tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
          bitIndex data) <=
      tokenSliceAtValuationBitBranchStructuralEnvelope valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset bitIndex := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let sourceAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    sourceStartTerm widthTerm
  let targetAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    targetStartTerm widthTerm
  cases data with
  | isFalse hsource htarget =>
      let sourceFalse := tokenSliceAtValuationBitAtomFalseCertificate
        valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
        hsource
      let targetFalse := tokenSliceAtValuationBitAtomFalseCertificate
        valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
        htarget
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := targetAtom) sourceFalse
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := sourceAtom) targetFalse
      have hsourceResource :=
        tokenSliceAtValuationBitAtomFalseCertificate_structuralPayloadBound_le_transparent
          valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
          hsource
      have htargetResource :=
        tokenSliceAtValuationBitAtomFalseCertificate_structuralPayloadBound_le_transparent
          valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
          htarget
      have hforward := transparentHybridDisjunctionLeftPayloadBound_le
        (right := targetAtom) sourceFalse _ hsourceResource
      have hbackward := transparentHybridDisjunctionLeftPayloadBound_le
        (right := sourceAtom) targetFalse _ htargetResource
      have hdirect := transparentHybridConjunctionPayloadBound_le
        forward backward _ _ hforward hbackward
      have hfromData :
          hybridFormulaStructuralPayloadBound
              (tokenSliceAtValuationBitBranchCertificateFromData valuation
                tokenTableTerm widthTerm sourceStartTerm targetStartTerm
                offset bitIndex (.isFalse hsource htarget)) <=
            tokenSliceAtValuationBitFalseBranchStructuralEnvelope valuation
              tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
              bitIndex := by
        simpa only [tokenSliceAtValuationBitBranchCertificateFromData,
          hybridFormulaStructuralPayloadBound,
          tokenSliceAtValuationBitFalseBranchStructuralEnvelope,
          branchValuation, sourceAtom, targetAtom, sourceFalse, targetFalse,
          forward, backward] using hdirect
      unfold tokenSliceAtValuationBitBranchStructuralEnvelope
      exact hfromData.trans (Nat.le_add_right _ _)
  | isTrue hsource htarget =>
      let sourceTrue := tokenSliceAtValuationBitAtomTrueCertificate
        valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
        hsource
      let targetTrue := tokenSliceAtValuationBitAtomTrueCertificate
        valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
        htarget
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼sourceAtom) targetTrue
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼targetAtom) sourceTrue
      have hsourceResource :=
        tokenSliceAtValuationBitAtomTrueCertificate_structuralPayloadBound_le_transparent
          valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
          hsource
      have htargetResource :=
        tokenSliceAtValuationBitAtomTrueCertificate_structuralPayloadBound_le_transparent
          valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
          htarget
      have hforward := transparentHybridDisjunctionRightPayloadBound_le
        (left := ∼sourceAtom) targetTrue _ htargetResource
      have hbackward := transparentHybridDisjunctionRightPayloadBound_le
        (left := ∼targetAtom) sourceTrue _ hsourceResource
      have hdirect := transparentHybridConjunctionPayloadBound_le
        forward backward _ _ hforward hbackward
      have hfromData :
          hybridFormulaStructuralPayloadBound
              (tokenSliceAtValuationBitBranchCertificateFromData valuation
                tokenTableTerm widthTerm sourceStartTerm targetStartTerm
                offset bitIndex (.isTrue hsource htarget)) <=
            tokenSliceAtValuationBitTrueBranchStructuralEnvelope valuation
              tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
              bitIndex := by
        simpa only [tokenSliceAtValuationBitBranchCertificateFromData,
          hybridFormulaStructuralPayloadBound,
          tokenSliceAtValuationBitTrueBranchStructuralEnvelope,
          branchValuation, sourceAtom, targetAtom, sourceTrue, targetTrue,
          forward, backward] using hdirect
      unfold tokenSliceAtValuationBitBranchStructuralEnvelope
      exact hfromData.trans (Nat.le_add_left _ _)

theorem tokenSliceAtValuationBitBranchCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat)
    (hbit : (termValue valuation tokenTableTerm).testBit
        ((termValue valuation sourceStartTerm + offset) *
          termValue valuation widthTerm + bitIndex) =
      (termValue valuation tokenTableTerm).testBit
        ((termValue valuation targetStartTerm + offset) *
          termValue valuation widthTerm + bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationBitBranchCertificate valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm offset bitIndex hbit) <=
      tokenSliceAtValuationBitBranchStructuralEnvelope valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset bitIndex := by
  simpa only [tokenSliceAtValuationBitBranchCertificate] using
    tokenSliceAtValuationBitBranchCertificateFromData_structuralPayloadBound_le_transparent
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
      bitIndex
      (tokenSliceAtValuationBitBranchDataOfEquality valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset bitIndex hbit)

noncomputable def tokenSliceAtValuationBitBranchPayloadResourceSum
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat) : Nat :=
  ∑ bitIndex : Fin (termValue valuation widthTerm),
    tokenSliceAtValuationBitBranchStructuralEnvelope valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset bitIndex

private theorem hybridBranchesLeafPayloadBound_transport
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {sourceBound targetBound leafBound : Nat}
    (hbound : sourceBound = targetBound)
    (branches : CheckedHybridValuationUniversalBranches valuation body
      sourceBound)
    (hleaves : HybridBranchesLeafPayloadBound leafBound branches) :
    HybridBranchesLeafPayloadBound leafBound (hbound ▸ branches) := by
  cases hbound
  exact hleaves

theorem tokenSliceAtValuationBitUniversalBranches_leafPayloadBound
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    HybridBranchesLeafPayloadBound
      (tokenSliceAtValuationBitBranchPayloadResourceSum valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset)
      (tokenSliceAtValuationBitUniversalBranches valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset hbits) := by
  let bound := termValue valuation widthTerm
  let branch := fun bitIndex hbitIndex =>
    CheckedHybridValuationBoundedFormulaCertificate.cast
      (tokenSliceAtValuationBitBody_free_alignment tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm).symm
      (tokenSliceAtValuationBitBranchCertificate valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset bitIndex
        (hbits bitIndex hbitIndex))
  let branches := buildExplicitHybridUniversalBranches bound branch
  have hraw : HybridBranchesLeafPayloadBound
      (tokenSliceAtValuationBitBranchPayloadResourceSum valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset)
      branches := by
    apply buildExplicitHybridUniversalBranches_leafPayloadBound
    intro bitIndex hbitIndex
    let finiteIndex : Fin bound := ⟨bitIndex, hbitIndex⟩
    have hleaf :=
      tokenSliceAtValuationBitBranchCertificate_structuralPayloadBound_le_transparent
        valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm
        offset bitIndex (hbits bitIndex hbitIndex)
    have hsum :
        tokenSliceAtValuationBitBranchStructuralEnvelope valuation
            tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
            finiteIndex <=
          tokenSliceAtValuationBitBranchPayloadResourceSum valuation
            tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset := by
      unfold tokenSliceAtValuationBitBranchPayloadResourceSum
      exact Finset.single_le_sum
        (fun (candidate : Fin bound) _ => Nat.zero_le
          (tokenSliceAtValuationBitBranchStructuralEnvelope valuation
            tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
            candidate))
        (Finset.mem_univ finiteIndex)
    dsimp only [branch, finiteIndex]
    simpa only [hybridFormulaStructuralPayloadBound] using hleaf.trans hsum
  have htransport := hybridBranchesLeafPayloadBound_transport
    (tokenSliceAtValuationBitBound_eq valuation widthTerm offset)
    branches hraw
  simpa only [tokenSliceAtValuationBitUniversalBranches, bound, branches,
    branch] using htransport

noncomputable def tokenSliceAtValuationBitBranchesTransparentEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat) : Nat :=
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue branchValuation boundTerm
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    branchValuation body
    (tokenSliceAtValuationBitBranchPayloadResourceSum valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset)
    bound

theorem tokenSliceAtValuationBitBranchesStructuralPayloadEnvelope_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    let branchValuation := extendValuation offset valuation
    let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
      sourceStartTerm targetStartTerm
    let boundTerm := Rew.shift widthTerm
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift boundTerm) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue branchValuation boundTerm) outerFormula.freeVariables
        (tokenSliceAtValuationBitUniversalBranches valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm offset hbits) <=
      tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset := by
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue branchValuation boundTerm
  let branches := tokenSliceAtValuationBitUniversalBranches valuation
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset hbits
  have hleaves := tokenSliceAtValuationBitUniversalBranches_leafPayloadBound
    valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
    hbits
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (tokenSliceAtValuationBitBranchPayloadResourceSum valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset)
    branches hleaves
  simpa only [tokenSliceAtValuationBitBranchesTransparentEnvelope,
    branchValuation, body, boundTerm, outerFormula, outerVariables, bound,
    branches] using hbound

noncomputable def tokenSliceAtValuationBitUniversalPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat) : Nat :=
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables branchValuation
  let bound := termValue branchValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset)
  compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound
    (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource branchValuation
      outerVariables boundTerm)
    branchResource

theorem tokenSliceAtValuationBitUniversalCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationBitUniversalCertificate valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm offset hbits) <=
      tokenSliceAtValuationBitUniversalPayloadEnvelope valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset := by
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables branchValuation
  let bound := termValue branchValuation boundTerm
  let branches := tokenSliceAtValuationBitUniversalBranches valuation
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset hbits
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope bound
    outerVariables branches
  let newBranchCore := tokenSliceAtValuationBitBranchesTransparentEnvelope
    valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    branchValuation outerVariables boundTerm
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body, boundTerm, branchValuation]
    exact tokenSliceAtValuationBitBranchesStructuralPayloadEnvelope_le_transparent
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
      hbits
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [tokenSliceAtValuationBitUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    tokenSliceAtValuationBitUniversalPayloadEnvelope,
    branchValuation, body, boundTerm, outerFormula, outerVariables, Gamma,
    bound, branches, oldBranchCore, newBranchCore, oldBranchResource,
    newBranchResource, boundResource] using htotal

theorem tokenSliceAtValuationOffsetBranchCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationOffsetBranchCertificate valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm offset hbits) <=
      tokenSliceAtValuationBitUniversalPayloadEnvelope valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset := by
  simpa only [tokenSliceAtValuationOffsetBranchCertificate,
    hybridFormulaStructuralPayloadBound] using
    tokenSliceAtValuationBitUniversalCertificate_structuralPayloadBound_le_transparent
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
      hbits

noncomputable def tokenSliceAtValuationOffsetBranchPayloadResourceSum
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat) : Nat :=
  ∑ offset : Fin count,
    tokenSliceAtValuationBitUniversalPayloadEnvelope valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset

theorem tokenSliceAtValuationOffsetUniversalBranches_leafPayloadBound
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    HybridBranchesLeafPayloadBound
      (tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm count)
      (tokenSliceAtValuationOffsetUniversalBranches valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm count hbits) := by
  let branch := fun offset hoffset =>
    tokenSliceAtValuationOffsetBranchCertificate valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset
      (hbits offset hoffset)
  let branches := buildExplicitHybridUniversalBranches count branch
  have hraw : HybridBranchesLeafPayloadBound
      (tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm count)
      branches := by
    apply buildExplicitHybridUniversalBranches_leafPayloadBound
    intro offset hoffset
    let finiteOffset : Fin count := ⟨offset, hoffset⟩
    have hleaf :=
      tokenSliceAtValuationOffsetBranchCertificate_structuralPayloadBound_le_transparent
        valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm
        offset (hbits offset hoffset)
    have hsum :
        tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
            tokenTableTerm widthTerm sourceStartTerm targetStartTerm
            finiteOffset <=
          tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
            tokenTableTerm widthTerm sourceStartTerm targetStartTerm count := by
      unfold tokenSliceAtValuationOffsetBranchPayloadResourceSum
      exact Finset.single_le_sum
        (fun (candidate : Fin count) _ => Nat.zero_le
          (tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
            tokenTableTerm widthTerm sourceStartTerm targetStartTerm candidate))
        (Finset.mem_univ finiteOffset)
    dsimp only [branch, finiteOffset]
    exact hleaf.trans hsum
  have htransport := hybridBranchesLeafPayloadBound_transport
    (tokenSliceAtValuationOffsetBound_eq valuation count) branches hraw
  simpa only [tokenSliceAtValuationOffsetUniversalBranches, branches,
    branch] using htransport

noncomputable def tokenSliceAtValuationOffsetBranchesTransparentEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat) : Nat :=
  let body := tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue valuation boundTerm
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables valuation
    body
    (tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm count)
    bound

theorem tokenSliceAtValuationOffsetBranchesStructuralPayloadEnvelope_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    let body := tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
      sourceStartTerm targetStartTerm
    let boundTerm := shortBinaryNumeralTerm count
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift boundTerm) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue valuation boundTerm) outerFormula.freeVariables
        (tokenSliceAtValuationOffsetUniversalBranches valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm count hbits) <=
      tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm count := by
  let body := tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue valuation boundTerm
  let branches := tokenSliceAtValuationOffsetUniversalBranches valuation
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm count hbits
  have hleaves :=
    tokenSliceAtValuationOffsetUniversalBranches_leafPayloadBound valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm count hbits
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm count)
    branches hleaves
  simpa only [tokenSliceAtValuationOffsetBranchesTransparentEnvelope,
    body, boundTerm, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def tokenSliceAtValuationOffsetUniversalPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat) : Nat :=
  let body := tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm count)
  compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound
    (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource valuation outerVariables
      boundTerm)
    branchResource

theorem tokenSliceAtValuationOffsetUniversalCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationOffsetUniversalCertificate valuation
          tokenTableTerm widthTerm sourceStartTerm targetStartTerm count hbits) <=
      tokenSliceAtValuationOffsetUniversalPayloadEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm count := by
  let body := tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation boundTerm
  let branches := tokenSliceAtValuationOffsetUniversalBranches valuation
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm count hbits
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope bound
    outerVariables branches
  let newBranchCore := tokenSliceAtValuationOffsetBranchesTransparentEnvelope
    valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm count
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource valuation
    outerVariables boundTerm
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body, boundTerm]
    exact
      tokenSliceAtValuationOffsetBranchesStructuralPayloadEnvelope_le_transparent
        valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm count
        hbits
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [tokenSliceAtValuationOffsetUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    tokenSliceAtValuationOffsetUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

noncomputable def tokenSliceAtValuationPostWitnessPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) : Nat :=
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm count) < !!tokenCountTerm + 1”
  let sourceEndpointFormula : ValuationFormula :=
    “!!sourceFinishTerm =
      !!sourceStartTerm + !!(shortBinaryNumeralTerm count)”
  let targetEndpointFormula : ValuationFormula :=
    “!!targetFinishTerm =
      !!targetStartTerm + !!(shortBinaryNumeralTerm count)”
  let sourceFinishFormula : ValuationFormula :=
    “!!sourceFinishTerm ≤ !!tokenCountTerm”
  let targetFinishFormula : ValuationFormula :=
    “!!targetFinishTerm ≤ !!tokenCountTerm”
  let offsetFormula := tokenSliceAtValuationOffsetUniversalFormula
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm count
  let countResource := tokenSliceAtValuationCountGuardStructuralEnvelope
    valuation tokenCountTerm count
  let sourceEndpointResource :=
    tokenSliceAtValuationEndpointStructuralEnvelope valuation sourceStartTerm
      sourceFinishTerm count
  let targetEndpointResource :=
    tokenSliceAtValuationEndpointStructuralEnvelope valuation targetStartTerm
      targetFinishTerm count
  let sourceFinishResource := tokenSliceAtValuationLeStructuralEnvelope
    valuation sourceFinishTerm tokenCountTerm
  let targetFinishResource := tokenSliceAtValuationLeStructuralEnvelope
    valuation targetFinishTerm tokenCountTerm
  let offsetResource := tokenSliceAtValuationOffsetUniversalPayloadEnvelope
    valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm count
  let targetFinishTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation targetFinishFormula offsetFormula targetFinishResource
    offsetResource
  let sourceFinishTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation sourceFinishFormula (targetFinishFormula ⋏ offsetFormula)
    sourceFinishResource targetFinishTailResource
  let targetEndpointTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation targetEndpointFormula
    (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula))
    targetEndpointResource sourceFinishTailResource
  let sourceEndpointTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation sourceEndpointFormula
    (targetEndpointFormula ⋏
      (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula)))
    sourceEndpointResource targetEndpointTailResource
  transparentHybridConjunctionPayloadEnvelope valuation countFormula
    (sourceEndpointFormula ⋏
      (targetEndpointFormula ⋏
        (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula))))
    countResource sourceEndpointTailResource

theorem tokenSliceAtValuationPostWitnessCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hcountBound : count <= termValue valuation tokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation tokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation tokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationPostWitnessCertificate valuation tokenTableTerm
          widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
          targetStartTerm targetFinishTerm count hcountBound hsourceEndpoint
          htargetEndpoint hsourceFinishBound htargetFinishBound hbits) <=
      tokenSliceAtValuationPostWitnessPayloadEnvelope valuation tokenTableTerm
        widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
        targetStartTerm targetFinishTerm count := by
  let countCertificate := tokenSliceAtValuationCountGuardCertificate valuation
    tokenCountTerm count hcountBound
  let sourceEndpointCertificate := tokenSliceAtValuationEndpointCertificate
    valuation sourceStartTerm sourceFinishTerm count hsourceEndpoint
  let targetEndpointCertificate := tokenSliceAtValuationEndpointCertificate
    valuation targetStartTerm targetFinishTerm count htargetEndpoint
  let sourceFinishCertificate := tokenSliceAtValuationLeCertificate valuation
    sourceFinishTerm tokenCountTerm hsourceFinishBound
  let targetFinishCertificate := tokenSliceAtValuationLeCertificate valuation
    targetFinishTerm tokenCountTerm htargetFinishBound
  let offsetCertificate := tokenSliceAtValuationOffsetUniversalCertificate
    valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm count
    hbits
  have hcount :=
    tokenSliceAtValuationCountGuardCertificate_structuralPayloadBound_le_transparent
      valuation tokenCountTerm count hcountBound
  have hsourceEndpointResource :=
    tokenSliceAtValuationEndpointCertificate_structuralPayloadBound_le_transparent
      valuation sourceStartTerm sourceFinishTerm count hsourceEndpoint
  have htargetEndpointResource :=
    tokenSliceAtValuationEndpointCertificate_structuralPayloadBound_le_transparent
      valuation targetStartTerm targetFinishTerm count htargetEndpoint
  have hsourceFinish :=
    tokenSliceAtValuationLeCertificate_structuralPayloadBound_le_transparent
      valuation sourceFinishTerm tokenCountTerm hsourceFinishBound
  have htargetFinish :=
    tokenSliceAtValuationLeCertificate_structuralPayloadBound_le_transparent
      valuation targetFinishTerm tokenCountTerm htargetFinishBound
  have hoffset :=
    tokenSliceAtValuationOffsetUniversalCertificate_structuralPayloadBound_le_transparent
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm count
      hbits
  let targetFinishTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetFinishCertificate offsetCertificate
  have htargetFinishTail := transparentHybridConjunctionPayloadBound_le
    targetFinishCertificate offsetCertificate _ _ htargetFinish hoffset
  let sourceFinishTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sourceFinishCertificate targetFinishTail
  have hsourceFinishTail := transparentHybridConjunctionPayloadBound_le
    sourceFinishCertificate targetFinishTail _ _ hsourceFinish
    htargetFinishTail
  let targetEndpointTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetEndpointCertificate sourceFinishTail
  have htargetEndpointTail := transparentHybridConjunctionPayloadBound_le
    targetEndpointCertificate sourceFinishTail _ _ htargetEndpointResource
    hsourceFinishTail
  let sourceEndpointTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sourceEndpointCertificate targetEndpointTail
  have hsourceEndpointTail := transparentHybridConjunctionPayloadBound_le
    sourceEndpointCertificate targetEndpointTail _ _ hsourceEndpointResource
    htargetEndpointTail
  let decomposed :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      countCertificate sourceEndpointTail
  have hdecomposed := transparentHybridConjunctionPayloadBound_le
    countCertificate sourceEndpointTail _ _ hcount hsourceEndpointTail
  simpa only [tokenSliceAtValuationPostWitnessCertificate,
    hybridFormulaStructuralPayloadBound,
    tokenSliceAtValuationPostWitnessPayloadEnvelope,
    countCertificate, sourceEndpointCertificate, targetEndpointCertificate,
    sourceFinishCertificate, targetFinishCertificate, offsetCertificate,
    targetFinishTail, sourceFinishTail, targetEndpointTail,
    sourceEndpointTail, decomposed] using hdecomposed

noncomputable def compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) : Nat :=
  hybridExistsWitnessStructuralPayloadEnvelope valuation
    (tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
    count
    (tokenSliceAtValuationPostWitnessPayloadEnvelope valuation tokenTableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm count)

noncomputable def
    compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope
    (bound : Nat)
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) : Nat :=
  (Finset.range (bound + 1)).sum fun count =>
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope valuation
      tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm count

theorem
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_publicFinite
    (bound : Nat)
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) (hcount : count <= bound) :
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope valuation
        tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
        targetStartTerm targetFinishTerm count <=
      compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope bound
        valuation tokenTableTerm widthTerm tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm := by
  unfold
    compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le
      (compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope valuation
        tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
        targetStartTerm targetFinishTerm candidate))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hcount))

theorem compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hcountBound : count <= termValue valuation tokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation tokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation tokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
          valuation tokenTableTerm widthTerm tokenCountTerm sourceStartTerm
          sourceFinishTerm targetStartTerm targetFinishTerm count hcountBound
          hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound
          hbits) <=
      compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope valuation
        tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
        targetStartTerm targetFinishTerm count := by
  let body := tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm
    tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
    targetFinishTerm
  let postCertificate := tokenSliceAtValuationPostWitnessCertificate valuation
    tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
    targetStartTerm targetFinishTerm count hcountBound hsourceEndpoint
    htargetEndpoint hsourceFinishBound htargetFinishBound hbits
  have hpost :=
    tokenSliceAtValuationPostWitnessCertificate_structuralPayloadBound_le_transparent
      valuation tokenTableTerm widthTerm tokenCountTerm sourceStartTerm
      sourceFinishTerm targetStartTerm targetFinishTerm count hcountBound
      hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound
      hbits
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope body
    count postCertificate
    (tokenSliceAtValuationPostWitnessPayloadEnvelope valuation tokenTableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm count) hpost
  simpa only [compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope,
    body, postCertificate] using hexists

theorem
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_publicFinite
    (bound : Nat)
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hcount : count <= bound)
    (hcountBound : count <= termValue valuation tokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation tokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation tokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
          valuation tokenTableTerm widthTerm tokenCountTerm sourceStartTerm
          sourceFinishTerm targetStartTerm targetFinishTerm count hcountBound
          hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound
          hbits) <=
      compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope bound
        valuation tokenTableTerm widthTerm tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm := by
  exact
    (compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      valuation tokenTableTerm widthTerm tokenCountTerm sourceStartTerm
      sourceFinishTerm targetStartTerm targetFinishTerm count hcountBound
      hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound
      hbits).trans
    (compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_publicFinite
      bound valuation tokenTableTerm widthTerm tokenCountTerm sourceStartTerm
      sourceFinishTerm targetStartTerm targetFinishTerm count hcount)

#print axioms
  tokenSliceAtValuationBitBranchCertificate_structuralPayloadBound_le_transparent
#print axioms
  tokenSliceAtValuationBitUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  tokenSliceAtValuationOffsetUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  tokenSliceAtValuationPostWitnessCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectTokenSlicePublicBounds
