import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
import integration.FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds

/-!
# Fully fixed invalid-tag selected branch of the syntax-formula parser

The eight checked tag disequalities are joined to the real syntax-term failure
certificate.  The right-associated nine-leaf formula is assembled with one
shared syntax-code coordinate and no coordinate-dependent public envelope.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaInvalidSelectedFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

private def invalidSelectedZeroValuation : Nat -> Nat := fun _ => 0

def syntaxFormulaInvalidSelectedCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  8 * parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxTermFailureClosedFormulaCodePolynomial numericBound bitBound + 72

def syntaxFormulaInvalidSelectedFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxFormulaInvalidSelectedCodePolynomial numericBound bitBound
  let atomicResource := parserFormulaNegativeAtomicFixedPayloadPolynomial
    bitBound
  let failureResource := syntaxTermFailureFullyFixedPayloadPolynomial
    numericBound bitBound
  let tailResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource failureResource
  hybridEightConjunctionCheckedGeneralPayloadEnvelope syntaxResource
    atomicResource atomicResource atomicResource atomicResource atomicResource
    atomicResource atomicResource tailResource

theorem
    syntaxFormulaInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (htag0 : witness.tag ≠ 0)
    (htag1 : witness.tag ≠ 1)
    (htag2 : witness.tag ≠ 2)
    (htag3 : witness.tag ≠ 3)
    (htag4 : witness.tag ≠ 4)
    (htag5 : witness.tag ≠ 5)
    (htag6 : witness.tag ≠ 6)
    (htag7 : witness.tag ≠ 7)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : witness.tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeNeCertificate witness.tag 0 htag0)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeNeCertificate witness.tag 1 htag1)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeNeCertificate witness.tag 2 htag2)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (nativeNeCertificate witness.tag 3 htag3)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeNeCertificate witness.tag 4 htag4)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (nativeNeCertificate witness.tag 5 htag5)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (nativeNeCertificate witness.tag 6 htag6)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (nativeNeCertificate witness.tag 7 htag7)
                        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                          tokenTable width tokenCount current next
                          witness.tailBoundary witness.tailCount
                          hfailure))))))))) <=
      syntaxFormulaInvalidSelectedFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let certificate0 := nativeNeCertificate witness.tag 0 htag0
  let certificate1 := nativeNeCertificate witness.tag 1 htag1
  let certificate2 := nativeNeCertificate witness.tag 2 htag2
  let certificate3 := nativeNeCertificate witness.tag 3 htag3
  let certificate4 := nativeNeCertificate witness.tag 4 htag4
  let certificate5 := nativeNeCertificate witness.tag 5 htag5
  let certificate6 := nativeNeCertificate witness.tag 6 htag6
  let certificate7 := nativeNeCertificate witness.tag 7 htag7
  let formula0 := nativeNeFormula witness.tag 0
  let formula1 := nativeNeFormula witness.tag 1
  let formula2 := nativeNeFormula witness.tag 2
  let formula3 := nativeNeFormula witness.tag 3
  let formula4 := nativeNeFormula witness.tag 4
  let formula5 := nativeNeFormula witness.tag 5
  let formula6 := nativeNeFormula witness.tag 6
  let formula7 := nativeNeFormula witness.tag 7
  let syntaxResource :=
    syntaxFormulaInvalidSelectedCodePolynomial numericBound bitBound
  let atomicResource :=
    parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound
  let failureResource :=
    syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound
  have hatomic0 :
      hybridFormulaStructuralPayloadBound certificate0 <= atomicResource := by
    dsimp only [certificate0, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 0
      bitBound htag0 htagSize (by omega)
  have hatomic1 :
      hybridFormulaStructuralPayloadBound certificate1 <= atomicResource := by
    dsimp only [certificate1, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 1
      bitBound htag1 htagSize (by omega)
  have hatomic2 :
      hybridFormulaStructuralPayloadBound certificate2 <= atomicResource := by
    dsimp only [certificate2, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 2
      bitBound htag2 htagSize (by omega)
  have hatomic3 :
      hybridFormulaStructuralPayloadBound certificate3 <= atomicResource := by
    dsimp only [certificate3, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 3
      bitBound htag3 htagSize (by omega)
  have hatomic4 :
      hybridFormulaStructuralPayloadBound certificate4 <= atomicResource := by
    dsimp only [certificate4, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 4
      bitBound htag4 htagSize (by omega)
  have hatomic5 :
      hybridFormulaStructuralPayloadBound certificate5 <= atomicResource := by
    dsimp only [certificate5, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 5
      bitBound htag5 htagSize (by omega)
  have hatomic6 :
      hybridFormulaStructuralPayloadBound certificate6 <= atomicResource := by
    dsimp only [certificate6, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 6
      bitBound htag6 htagSize (by omega)
  have hatomic7 :
      hybridFormulaStructuralPayloadBound certificate7 <= atomicResource := by
    dsimp only [certificate7, atomicResource]
    exact nativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 7
      bitBound htag7 htagSize (by omega)
  have hfailureResource :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        failureResource := by
    dsimp only [failureCertificate, failureResource]
    exact
      compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount numericBound bitBound hfailure hwidth htokenCount
        htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
        htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
        hbitPositive
  have hatomicCode (expected : Nat) (hexpected : expected <= 7) :
      (binaryFormulaCode (nativeNeFormula witness.tag expected)).length <=
        syntaxResource := by
    have hcode := nativeNeFormula_code_length_le_fixed witness.tag expected
      bitBound htagSize hexpected
    dsimp only [syntaxResource]
    unfold syntaxFormulaInvalidSelectedCodePolynomial
    omega
  have hfailureCodeBase :
      (binaryFormulaCode failureFormula).length <=
        syntaxTermFailureClosedFormulaCodePolynomial numericBound
          bitBound := by
    dsimp only [failureFormula, syntaxResource]
    exact
      syntaxTermFailureClosedFormula_code_length_le_fixed tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount
        numericBound bitBound hfailure hwidth htokenCount htailCount
        hcurrentValue htokenTableSize hwidthSize htokenCountSize hcurrentSize
        hnextSize htailBoundarySize hnumericSize
  have hfailureCode :
      (binaryFormulaCode failureFormula).length <= syntaxResource := by
    have hcode := hfailureCodeBase
    dsimp only [syntaxResource]
    unfold syntaxFormulaInvalidSelectedCodePolynomial
    omega
  have htotalCode :
      (binaryFormulaCode
        (formula0 ⋏
          (formula1 ⋏
            (formula2 ⋏
              (formula3 ⋏
                (formula4 ⋏
                  (formula5 ⋏
                    (formula6 ⋏ (formula7 ⋏ failureFormula))))))))).length <=
        syntaxResource := by
    have h0 := nativeNeFormula_code_length_le_fixed witness.tag 0 bitBound
      htagSize (by omega)
    have h1 := nativeNeFormula_code_length_le_fixed witness.tag 1 bitBound
      htagSize (by omega)
    have h2 := nativeNeFormula_code_length_le_fixed witness.tag 2 bitBound
      htagSize (by omega)
    have h3 := nativeNeFormula_code_length_le_fixed witness.tag 3 bitBound
      htagSize (by omega)
    have h4 := nativeNeFormula_code_length_le_fixed witness.tag 4 bitBound
      htagSize (by omega)
    have h5 := nativeNeFormula_code_length_le_fixed witness.tag 5 bitBound
      htagSize (by omega)
    have h6 := nativeNeFormula_code_length_le_fixed witness.tag 6 bitBound
      htagSize (by omega)
    have h7 := nativeNeFormula_code_length_le_fixed witness.tag 7 bitBound
      htagSize (by omega)
    have hfailure := hfailureCodeBase
    have hconjunctionTag : (binaryNatCode 4).length <= 8 := by decide
    dsimp only [formula0, formula1, formula2, formula3, formula4, formula5,
      formula6, formula7, syntaxResource]
    simp only [binaryFormulaCode, List.length_append] at *
    unfold syntaxFormulaInvalidSelectedCodePolynomial
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold syntaxFormulaInvalidSelectedCodePolynomial
    omega
  have hclosed0 : formula0.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 0
  have hclosed1 : formula1.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 1
  have hclosed2 : formula2.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 2
  have hclosed3 : formula3.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 3
  have hclosed4 : formula4.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 4
  have hclosed5 : formula5.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 5
  have hclosed6 : formula6.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 6
  have hclosed7 : formula7.freeVariables = ∅ := by
    exact nativeNeFormula_freeVariables_eq_empty_fixed witness.tag 7
  have hfailureClosed : failureFormula.freeVariables = ∅ := by
    dsimp only [failureFormula]
    exact syntaxTermFailureClosedFormula_freeVariables_eq_empty tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate7
      failureCertificate
  let tailFormula := formula7 ⋏ failureFormula
  let tailResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource failureResource
  have htailTransparent :=
    transparentHybridConjunctionPayloadBound_le certificate7
      failureCertificate atomicResource failureResource hatomic7
      hfailureResource
  have htailCode :
      (binaryFormulaCode tailFormula).length <= syntaxResource := by
    have hraw := FoundationCompactListedLocalCostPrimitives.binaryFormulaCode_and_length_le
      formula7 failureFormula
    have h7 := nativeNeFormula_code_length_le_fixed witness.tag 7 bitBound
      htagSize (by omega)
    dsimp only [tailFormula, formula7] at *
    have hfailure := hfailureCodeBase
    dsimp only [syntaxResource] at *
    unfold syntaxFormulaInvalidSelectedCodePolynomial at *
    omega
  have htailClosed : tailFormula.freeVariables = ∅ := by
    dsimp only [tailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed7,
      hfailureClosed]
    simp
  have htailGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      invalidSelectedZeroValuation formula7 failureFormula atomicResource
      failureResource syntaxResource hpositive hclosed7 hfailureClosed
      (hatomicCode 7 (by omega)) hfailureCode htailCode
  have htail :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource := by
    exact htailTransparent.trans htailGeneral
  have hall :=
    checkedHybridEightConjunctionPayloadBound_le_closedGeneral certificate0
      certificate1 certificate2 certificate3 certificate4 certificate5
      certificate6 tailCertificate atomicResource atomicResource
      atomicResource atomicResource atomicResource atomicResource
      atomicResource tailResource syntaxResource hatomic0 hatomic1 hatomic2
      hatomic3 hatomic4 hatomic5 hatomic6 htail hpositive hclosed0 hclosed1
      hclosed2 hclosed3 hclosed4 hclosed5 hclosed6 htailClosed (by
        simpa only [tailFormula] using htotalCode)
  unfold syntaxFormulaInvalidSelectedFullyFixedPayloadPolynomial
  simpa only [certificate0, certificate1, certificate2, certificate3,
    certificate4, certificate5, certificate6, certificate7,
    failureCertificate, tailCertificate, formula0, formula1, formula2,
    formula3, formula4, formula5, formula6, formula7, failureFormula,
    tailFormula, syntaxResource, atomicResource, failureResource,
    tailResource, invalidSelectedZeroValuation] using hall

#print axioms
  syntaxFormulaInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaInvalidSelectedFullyFixedBounds
