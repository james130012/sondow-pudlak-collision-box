import integration.FoundationCompactNumericListedDirectNegationFormulaTagWitnessExistsFixedBounds
import integration.FoundationCompactNumericListedDirectNegationFormulaTagEightLeFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fixed outer branch assembly for the complete negation-tag certificate

All subformula code and closedness facts are extracted from the already proved
bound for the complete closed formula.  The three semantic branches then pay
only general conjunction/disjunction assembly costs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagBranchAssemblyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagFormulaFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagEightLeFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagWitnessExistsFixedBounds

private abbrev tagZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation

def negationFormulaTagOuterSyntaxPolynomial (bitBound : Nat) : Nat :=
  compactNegationFormulaTagFullFormulaCodePolynomial bitBound + 1

def negationFormulaTagSmallWitnessDisjunctionPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (negationFormulaTagOuterSyntaxPolynomial bitBound)
    (negationFormulaTagWitnessExistsFixedPayloadPolynomial bitBound)

def negationFormulaTagSmallBranchPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (negationFormulaTagOuterSyntaxPolynomial bitBound)
    (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)
    (negationFormulaTagSmallWitnessDisjunctionPayloadPolynomial bitBound)

def negationFormulaTagSmallOuterPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (negationFormulaTagOuterSyntaxPolynomial bitBound)
    (negationFormulaTagSmallBranchPayloadPolynomial bitBound)

def negationFormulaTagLargeBranchPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (negationFormulaTagOuterSyntaxPolynomial bitBound)
    (negationFormulaTagEightLeFixedPayloadPolynomial bitBound)
    (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)

def negationFormulaTagLargeOuterPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (negationFormulaTagOuterSyntaxPolynomial bitBound)
    (negationFormulaTagLargeBranchPayloadPolynomial bitBound)

def negationFormulaTagFullyFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  negationFormulaTagSmallOuterPayloadPolynomial bitBound +
    negationFormulaTagLargeOuterPayloadPolynomial bitBound

private theorem binaryFormulaCode_and_left_le_tagOuter
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_tagOuter
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_or_left_le_tagOuter
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_or_right_le_tagOuter
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem conjunction_left_closed_tagOuter
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

private theorem conjunction_right_closed_tagOuter
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

private theorem disjunction_left_closed_tagOuter
    (left right : ValuationFormula)
    (hclosed : (left ⋎ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

private theorem disjunction_right_closed_tagOuter
    (left right : ValuationFormula)
    (hclosed : (left ⋎ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

theorem
    compactNegationFormulaTagExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
    (tag mapped bitBound : Nat)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound)
    (data : CompactNegationFormulaTagCheckedBranchData tag mapped) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagExplicitHybridCertificateFromData
          tag mapped data) <=
      negationFormulaTagFullyFixedPayloadPolynomial bitBound := by
  let tagLtFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) < 8”
  let evenFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped
  let oddFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped
  let witnessFormula := evenFormula ⋎ oddFormula
  let smallFormula := tagLtFormula ⋏ witnessFormula
  let eightLeFormula : ValuationFormula :=
    “8 ≤ !!(shortBinaryNumeralTerm tag)”
  let mappedFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm mapped) = !!(shortBinaryNumeralTerm tag)”
  let largeFormula := eightLeFormula ⋏ mappedFormula
  let fullFormula := smallFormula ⋎ largeFormula
  let syntaxResource := negationFormulaTagOuterSyntaxPolynomial bitBound
  let atomResource := negationFormulaTagAtomicFixedPayloadPolynomial bitBound
  let existsResource :=
    negationFormulaTagWitnessExistsFixedPayloadPolynomial bitBound
  let witnessResource :=
    negationFormulaTagSmallWitnessDisjunctionPayloadPolynomial bitBound
  let smallResource :=
    negationFormulaTagSmallBranchPayloadPolynomial bitBound
  let largeResource :=
    negationFormulaTagLargeBranchPayloadPolynomial bitBound
  have hfullAlignment :
      fullFormula = compactNegationFormulaTagExplicitFormula tag mapped := by
    rfl
  have hfullClosed : fullFormula.freeVariables = ∅ := by
    rw [hfullAlignment, ← compactNegationFormulaTagClosedFormula_alignment]
    exact compactNegationFormulaTagClosedFormula_closed tag mapped
  have hfullCode : (binaryFormulaCode fullFormula).length <=
      syntaxResource := by
    have hraw := compactNegationFormulaTagClosedFormula_code_length_le_fixed
      tag mapped bitBound htagSize hmappedSize
    rw [hfullAlignment, ← compactNegationFormulaTagClosedFormula_alignment]
    dsimp only [syntaxResource]
    unfold negationFormulaTagOuterSyntaxPolynomial
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold negationFormulaTagOuterSyntaxPolynomial
    omega
  have hsmallClosed := disjunction_left_closed_tagOuter smallFormula
    largeFormula hfullClosed
  have hlargeClosed := disjunction_right_closed_tagOuter smallFormula
    largeFormula hfullClosed
  have htagLtClosed := conjunction_left_closed_tagOuter tagLtFormula
    witnessFormula hsmallClosed
  have hwitnessClosed := conjunction_right_closed_tagOuter tagLtFormula
    witnessFormula hsmallClosed
  have hevenClosed := disjunction_left_closed_tagOuter evenFormula oddFormula
    hwitnessClosed
  have hoddClosed := disjunction_right_closed_tagOuter evenFormula oddFormula
    hwitnessClosed
  have heightLeClosed := conjunction_left_closed_tagOuter eightLeFormula
    mappedFormula hlargeClosed
  have hmappedClosed := conjunction_right_closed_tagOuter eightLeFormula
    mappedFormula hlargeClosed
  have hsmallCode := (binaryFormulaCode_or_left_le_tagOuter smallFormula
    largeFormula).trans hfullCode
  have hlargeCode := (binaryFormulaCode_or_right_le_tagOuter smallFormula
    largeFormula).trans hfullCode
  have htagLtCode := (binaryFormulaCode_and_left_le_tagOuter tagLtFormula
    witnessFormula).trans hsmallCode
  have hwitnessCode := (binaryFormulaCode_and_right_le_tagOuter tagLtFormula
    witnessFormula).trans hsmallCode
  have hevenCode := (binaryFormulaCode_or_left_le_tagOuter evenFormula
    oddFormula).trans hwitnessCode
  have hoddCode := (binaryFormulaCode_or_right_le_tagOuter evenFormula
    oddFormula).trans hwitnessCode
  have heightLeCode := (binaryFormulaCode_and_left_le_tagOuter eightLeFormula
    mappedFormula).trans hlargeCode
  have hmappedCode := (binaryFormulaCode_and_right_le_tagOuter eightLeFormula
    mappedFormula).trans hlargeCode
  have hwitnessLeftAssembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_general
      tagZeroValuation evenFormula oddFormula existsResource syntaxResource
      hpositive (by
        rw [hwitnessClosed]
        simp [valuationContext,
          FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum])
      hevenCode hoddCode hwitnessCode
  have hwitnessRightAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general
      tagZeroValuation evenFormula oddFormula existsResource syntaxResource
      hpositive (by
        rw [hwitnessClosed]
        simp [valuationContext,
          FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum])
      hevenCode hoddCode hwitnessCode
  have hsmallAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      tagZeroValuation tagLtFormula witnessFormula atomResource
      witnessResource syntaxResource hpositive htagLtClosed hwitnessClosed
      htagLtCode hwitnessCode hsmallCode
  have hlargeAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      tagZeroValuation eightLeFormula mappedFormula
      (negationFormulaTagEightLeFixedPayloadPolynomial bitBound) atomResource
      syntaxResource hpositive heightLeClosed hmappedClosed heightLeCode
      hmappedCode hlargeCode
  have houterLeftAssembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_general
      tagZeroValuation smallFormula largeFormula smallResource syntaxResource
      hpositive (by
        rw [hfullClosed]
        simp [valuationContext,
          FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum])
      hsmallCode hlargeCode hfullCode
  have houterRightAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general
      tagZeroValuation smallFormula largeFormula largeResource syntaxResource
      hpositive (by
        rw [hfullClosed]
        simp [valuationContext,
          FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum])
      hsmallCode hlargeCode hfullCode
  cases data with
  | even hsmall pair hpair htag hmapped =>
      let evenCertificate :=
        compactNegationFormulaTagEvenWitnessCertificate
          tag mapped pair hpair htag hmapped
      let witnessCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := oddFormula) evenCertificate
      let tagCertificate := tagLtEightCertificate tag hsmall
      let smallCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          tagCertificate witnessCertificate
      have hevenResource :=
        evenWitnessCertificate_structuralPayloadBound_le_fixed
          tag mapped pair bitBound hpair htag hmapped htagSize hmappedSize
      have hwitnessRaw := transparentHybridDisjunctionLeftPayloadBound_le
        (right := oddFormula) evenCertificate existsResource hevenResource
      have hwitnessFixed :
          hybridFormulaStructuralPayloadBound witnessCertificate <=
            witnessResource := by
        exact hwitnessRaw.trans (by
          dsimp only [witnessResource]
          exact hwitnessLeftAssembly)
      have htagResource :=
        tagLtEightCertificate_structuralPayloadBound_le_fixed tag bitBound
          hsmall htagSize
      have hsmallRaw := transparentHybridConjunctionPayloadBound_le
        tagCertificate witnessCertificate atomResource witnessResource
        htagResource hwitnessFixed
      have hsmallFixed :
          hybridFormulaStructuralPayloadBound smallCertificate <=
            smallResource := hsmallRaw.trans (by
        dsimp only [smallResource]
        exact hsmallAssembly)
      have houterRaw := transparentHybridDisjunctionLeftPayloadBound_le
        (right := largeFormula) smallCertificate smallResource hsmallFixed
      have houterFixed := houterRaw.trans (by
        dsimp only [smallResource]
        exact houterLeftAssembly)
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := largeFormula) smallCertificate) <= _
      have hnamed :
          hybridFormulaStructuralPayloadBound
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := largeFormula) smallCertificate) <=
            negationFormulaTagSmallOuterPayloadPolynomial bitBound := by
        simpa only [negationFormulaTagSmallOuterPayloadPolynomial,
          smallResource, syntaxResource] using houterFixed
      exact hnamed.trans (by
        unfold negationFormulaTagFullyFixedPayloadPolynomial
        exact Nat.le_add_right _ _)
  | odd hsmall pair hpair htag hmapped =>
      let oddCertificate :=
        compactNegationFormulaTagOddWitnessCertificate
          tag mapped pair hpair htag hmapped
      let witnessCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := evenFormula) oddCertificate
      let tagCertificate := tagLtEightCertificate tag hsmall
      let smallCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          tagCertificate witnessCertificate
      have hoddResource :=
        oddWitnessCertificate_structuralPayloadBound_le_fixed
          tag mapped pair bitBound hpair htag hmapped htagSize hmappedSize
      have hwitnessRaw := transparentHybridDisjunctionRightPayloadBound_le
        (left := evenFormula) oddCertificate existsResource hoddResource
      have hwitnessFixed :
          hybridFormulaStructuralPayloadBound witnessCertificate <=
            witnessResource := by
        exact hwitnessRaw.trans (by
          dsimp only [witnessResource]
          exact hwitnessRightAssembly)
      have htagResource :=
        tagLtEightCertificate_structuralPayloadBound_le_fixed tag bitBound
          hsmall htagSize
      have hsmallRaw := transparentHybridConjunctionPayloadBound_le
        tagCertificate witnessCertificate atomResource witnessResource
        htagResource hwitnessFixed
      have hsmallFixed :
          hybridFormulaStructuralPayloadBound smallCertificate <=
            smallResource := hsmallRaw.trans (by
        dsimp only [smallResource]
        exact hsmallAssembly)
      have houterRaw := transparentHybridDisjunctionLeftPayloadBound_le
        (right := largeFormula) smallCertificate smallResource hsmallFixed
      have houterFixed := houterRaw.trans (by
        dsimp only [smallResource]
        exact houterLeftAssembly)
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := largeFormula) smallCertificate) <= _
      have hnamed :
          hybridFormulaStructuralPayloadBound
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := largeFormula) smallCertificate) <=
            negationFormulaTagSmallOuterPayloadPolynomial bitBound := by
        simpa only [negationFormulaTagSmallOuterPayloadPolynomial,
          smallResource, syntaxResource] using houterFixed
      exact hnamed.trans (by
        unfold negationFormulaTagFullyFixedPayloadPolynomial
        exact Nat.le_add_right _ _)
  | large hlarge hmapped =>
      let lowerCertificate := eightLeTagCertificate tag hlarge
      let equalityCertificate :=
        mappedTagEqualityCertificate tag mapped hmapped
      let largeCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          lowerCertificate equalityCertificate
      have hlowerResource :=
        eightLeTagCertificate_structuralPayloadBound_le_fixed tag bitBound
          hlarge htagSize
      have hequalityResource :=
        mappedTagEqualityCertificate_structuralPayloadBound_le_fixed
          tag mapped bitBound hmapped htagSize hmappedSize
      have hlargeRaw := transparentHybridConjunctionPayloadBound_le
        lowerCertificate equalityCertificate
        (negationFormulaTagEightLeFixedPayloadPolynomial bitBound)
        atomResource hlowerResource hequalityResource
      have hlargeFixed :
          hybridFormulaStructuralPayloadBound largeCertificate <=
            largeResource := hlargeRaw.trans (by
        dsimp only [largeResource]
        exact hlargeAssembly)
      have houterRaw := transparentHybridDisjunctionRightPayloadBound_le
        (left := smallFormula) largeCertificate largeResource hlargeFixed
      have houterFixed := houterRaw.trans (by
        dsimp only [largeResource]
        exact houterRightAssembly)
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := smallFormula) largeCertificate) <= _
      have hnamed :
          hybridFormulaStructuralPayloadBound
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := smallFormula) largeCertificate) <=
            negationFormulaTagLargeOuterPayloadPolynomial bitBound := by
        simpa only [negationFormulaTagLargeOuterPayloadPolynomial,
          largeResource, syntaxResource] using houterFixed
      exact hnamed.trans (by
        unfold negationFormulaTagFullyFixedPayloadPolynomial
        exact Nat.le_add_left _ _)

#print axioms
  compactNegationFormulaTagExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNegationFormulaTagBranchAssemblyFixedBounds
