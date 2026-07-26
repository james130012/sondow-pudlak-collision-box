import integration.FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren

/-! # Fully fixed direct proof for natural-list witness rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren

def compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    compactNatSizeFixedPayloadPolynomial bitBound +
    parserAreaFixedPayloadPolynomial bitBound +
    3 * (binaryNatCode 4).length + 1

def compactNatListWitnessRowsFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial numericBound
      bitBound
  compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    compactNatSizeFixedPayloadPolynomial bitBound +
    parserAreaFixedPayloadPolynomial bitBound +
    9 * generalContextAssemblyEnvelope syntaxResource

noncomputable def compactNatListWitnessRowsFullyFixedBound
    (tokenTable width tokenCount start count finish boundaryTable boundarySize
      numericBound bitBound : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ClosedDirectFormulaBound
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
        tokenCount start count finish boundaryTable boundarySize)
      (compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound
        bitBound) := by
  rcases hrows with ⟨hlayout, hunit, hsize, harea⟩
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount start count finish boundaryTable
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula tokenCount
    count boundaryTable
  let sizeFormula := compactNatSizeClosedFormula boundarySize boundaryTable
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm boundarySize) ≤
      (!!(shortBinaryNumeralTerm count) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let layoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let unitResource :=
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  let sizeResource := compactNatSizeFixedPayloadPolynomial bitBound
  let areaResource := parserAreaFixedPayloadPolynomial bitBound
  let syntaxResource :=
    compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial numericBound
      bitBound
  let layoutBound := compactNatListWitnessRowsLayoutFixedBound tokenTable width
    tokenCount start count finish boundaryTable numericBound bitBound hlayout
    hwidthBound htokenCount hcount htokenTableSize hboundaryTableSize
    hnumericSize
  let unitBound := compactNatListWitnessRowsUnitFixedBound tokenCount count
    boundaryTable numericBound bitBound hunit htokenCount hcount
    hboundaryTableSize hnumericSize
  let sizeBound := compactNatListWitnessRowsSizeFixedBound boundarySize
    boundaryTable bitBound hsize hboundaryTableSize
  let areaBound := compactNatListWitnessRowsAreaFixedBound tokenCount count
    boundaryTable boundarySize numericBound bitBound hsize harea htokenCount
    hcount hboundaryTableSize hnumericSize
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
    omega
  let sizeAreaFormula := sizeFormula ⋏ areaFormula
  let sizeAreaResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource sizeResource areaResource
  let sizeAreaCode := sizeResource + areaResource + (binaryNatCode 4).length
  let sizeAreaBound : FixedClosedDirectFormulaBound sizeAreaFormula
      sizeAreaResource sizeAreaCode :=
    FixedClosedDirectFormulaBound.conjunction sizeBound areaBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, sizeResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, areaResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, sizeResource, areaResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega)
  let unitTailFormula := unitFormula ⋏ sizeAreaFormula
  let unitTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource unitResource sizeAreaResource
  let unitTailCode := unitResource + sizeAreaCode + (binaryNatCode 4).length
  let unitTailBound : FixedClosedDirectFormulaBound unitTailFormula
      unitTailResource unitTailCode :=
    FixedClosedDirectFormulaBound.conjunction unitBound sizeAreaBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, unitResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, sizeAreaCode, sizeResource, areaResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, unitResource, sizeAreaCode, sizeResource,
          areaResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega)
  let partsFormula := layoutFormula ⋏ unitTailFormula
  let partsResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    layoutResource unitTailResource
  let partsCode := layoutResource + unitTailCode + (binaryNatCode 4).length
  let partsBound : FixedClosedDirectFormulaBound partsFormula partsResource
      partsCode :=
    FixedClosedDirectFormulaBound.conjunction layoutBound unitTailBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, layoutResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, unitTailCode, unitResource, sizeAreaCode,
          sizeResource, areaResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, layoutResource, unitTailCode, unitResource,
          sizeAreaCode, sizeResource, areaResource]
        unfold compactNatListWitnessRowsFullyFixedAssemblySyntaxPolynomial
        omega)
  let explicitFormula := compactAdditiveNatListWitnessRowsPartsFormula
    tokenTable width tokenCount start count finish boundaryTable boundarySize
  have hparts : partsFormula = explicitFormula := by rfl
  let explicitProof := CertifiedPAContextProof.cast hparts partsBound.proof
  let closedFormula := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount start count finish boundaryTable boundarySize
  have hformula : explicitFormula = closedFormula :=
    (compactAdditiveNatListWitnessRowsClosedFormula_alignment tokenTable width
      tokenCount start count finish boundaryTable boundarySize).symm
  let formulaProof := CertifiedPAContextProof.cast hformula explicitProof
  have hcontext : valuationContext partsFormula.freeVariables
      parserFixedZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [partsBound.closed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext formulaProof
  refine { proof := proof, payloadLength_le := ?_ }
  have hexplicitLength : explicitProof.payloadLength =
      partsBound.proof.payloadLength := by
    dsimp only [explicitProof]
    exact CertifiedPAContextProof.cast_payloadLength hparts partsBound.proof
  have hformulaLength : formulaProof.payloadLength =
      partsBound.proof.payloadLength := by
    dsimp only [formulaProof]
    rw [CertifiedPAContextProof.cast_payloadLength]
    exact hexplicitLength
  have hproofLength : proof.payloadLength =
      partsBound.proof.payloadLength := by
    dsimp only [proof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hformulaLength
  rw [hproofLength]
  apply partsBound.payloadLength_le.trans
  dsimp only [partsResource, unitTailResource, sizeAreaResource,
    layoutResource, unitResource, sizeResource, areaResource, syntaxResource]
  unfold hybridConjunctionGeneralPayloadEnvelope
    compactNatListWitnessRowsFullyFixedPayloadPolynomial
  dsimp only
  omega

noncomputable def compileCompactNatListWitnessRowsFullyFixed
    (tokenTable width tokenCount start count finish boundaryTable boundarySize
      numericBound bitBound : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :=
  (compactNatListWitnessRowsFullyFixedBound tokenTable width tokenCount start
    count finish boundaryTable boundarySize numericBound bitBound hrows
    hwidthBound htokenCount hcount htokenTableSize hboundaryTableSize
    hnumericSize).proof

theorem compileCompactNatListWitnessRowsFullyFixed_payloadLength_le
    (tokenTable width tokenCount start count finish boundaryTable boundarySize
      numericBound bitBound : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactNatListWitnessRowsFullyFixed tokenTable width tokenCount
      start count finish boundaryTable boundarySize numericBound bitBound
      hrows hwidthBound htokenCount hcount htokenTableSize hboundaryTableSize
      hnumericSize).payloadLength <=
      compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound
        bitBound :=
  (compactNatListWitnessRowsFullyFixedBound tokenTable width tokenCount start
    count finish boundaryTable boundarySize numericBound bitBound hrows
    hwidthBound htokenCount hcount htokenTableSize hboundaryTableSize
    hnumericSize).payloadLength_le

#print axioms compactNatListWitnessRowsFullyFixedBound
#print axioms compileCompactNatListWitnessRowsFullyFixed_payloadLength_le

end FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof
