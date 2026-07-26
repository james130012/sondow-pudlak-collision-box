import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

/-! # Fully fixed child proofs for natural-list witness rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

noncomputable def compactNatListWitnessRowsLayoutFixedBound
    (tokenTable width tokenCount start count finish boundaryTable
      numericBound bitBound : Nat)
    (hlayout : CompactAdditiveStructuredListLayout tokenTable width tokenCount
      start count finish boundaryTable)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    FixedClosedDirectFormulaBound
      (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
        tokenCount start count finish boundaryTable)
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound)
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound) := by
  let data := compactAdditiveStructuredListLayoutDataOfLayout tokenTable width
    tokenCount start count finish boundaryTable hlayout
  let proof :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount start count finish boundaryTable
      data.bodyStart numericBound bitBound data.bodyStart_le_tokenCount
      data.header data.boundaryFinish_le_tokenCount data.boundaryStartEntry
      data.boundaryFinishEntry data.rows htokenCount hcount
      hboundaryTableSize hnumericSize
  have hpayload : proof.payloadLength <=
      compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound := by
    exact
      compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
        tokenTable width tokenCount start count finish boundaryTable
        data.bodyStart numericBound bitBound data.bodyStart_le_tokenCount
        data.header data.boundaryFinish_le_tokenCount data.boundaryStartEntry
        data.boundaryFinishEntry data.rows hwidthBound htokenCount hcount
        htokenTableSize hboundaryTableSize hnumericSize
  have hclosed :=
    compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount start count finish boundaryTable
  exact fixedClosedDirectFormulaBoundOfEmptyProof proof _ hpayload hclosed

noncomputable def compactNatListWitnessRowsUnitFixedBound
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hunit : CompactAdditiveUnitBoundaryRows tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    FixedClosedDirectFormulaBound
      (compactAdditiveUnitBoundaryRowsClosedFormula tokenCount count
        boundaryTable)
      (unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
        bitBound)
      (unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
        bitBound) := by
  let proof :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount count boundaryTable numericBound bitBound hunit htokenCount
      hcount hboundaryTableSize hnumericSize
  have hpayload : proof.payloadLength <=
      unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
        bitBound :=
    (compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
      tokenCount count boundaryTable numericBound bitBound hunit htokenCount
      hcount hboundaryTableSize hnumericSize).trans
      (compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource_le_fixed
        tokenCount count boundaryTable numericBound bitBound htokenCount hcount
        hboundaryTableSize hnumericSize)
  have hclosed :=
    compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
      tokenCount count boundaryTable
  exact fixedClosedDirectFormulaBoundOfEmptyProof proof _ hpayload hclosed

noncomputable def compactNatListWitnessRowsSizeFixedBound
    (boundarySize boundaryTable bitBound : Nat)
    (hsize : boundarySize = Nat.size boundaryTable)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound) :
    FixedClosedDirectFormulaBound
      (compactNatSizeClosedFormula boundarySize boundaryTable)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound) := by
  let certificate := compactNatSizeExplicitHybridCertificateOfEq boundarySize
    boundaryTable hsize
  have hpayload : certificate.compile.payloadLength <=
      compactNatSizeFixedPayloadPolynomial bitBound :=
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        boundarySize boundaryTable hsize).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed boundarySize
          boundaryTable bitBound hsize hboundaryTableSize))
  have hclosed := natSizeClosedFormula_freeVariables_eq_empty boundarySize
    boundaryTable
  exact fixedClosedDirectFormulaBoundOfProof certificate.compile _ hpayload
    hclosed

noncomputable def compactNatListWitnessRowsAreaFixedBound
    (tokenCount count boundaryTable boundarySize numericBound bitBound : Nat)
    (hsize : boundarySize = Nat.size boundaryTable)
    (harea : boundarySize <= (count + 1) * tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    FixedClosedDirectFormulaBound
      (“!!(shortBinaryNumeralTerm boundarySize) ≤
        (!!(shortBinaryNumeralTerm count) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)
      (parserAreaFixedPayloadPolynomial bitBound)
      (parserAreaFixedPayloadPolynomial bitBound) := by
  let certificate := boundaryAreaCertificate boundarySize count tokenCount
    harea
  have hpayload : certificate.compile.payloadLength <=
      parserAreaFixedPayloadPolynomial bitBound :=
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      ((boundaryAreaCertificate_structuralPayloadBound_le_public boundarySize
        count tokenCount harea).trans
        (boundaryAreaStructuralPayloadPolynomial_le_fixed boundarySize count
          tokenCount boundaryTable numericBound bitBound hsize htokenCount
          hcount hboundaryTableSize hnumericSize))
  have hclosed := parserAreaFormula_freeVariables_eq_empty boundarySize count
    tokenCount
  exact fixedClosedDirectFormulaBoundOfProof certificate.compile _ hpayload
    hclosed

#print axioms compactNatListWitnessRowsLayoutFixedBound
#print axioms compactNatListWitnessRowsUnitFixedBound
#print axioms compactNatListWitnessRowsSizeFixedBound
#print axioms compactNatListWitnessRowsAreaFixedBound

end FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren
