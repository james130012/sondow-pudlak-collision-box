import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsClosedGeneralBounds

/-! # Fully fixed bound for the complete clean syntax-formula parser graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsClosedGeneralBounds

theorem
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph
          tokenTable width tokenCount current next binderArity witness hgraph) <=
      cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hparts :=
    compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize htailBoundarySize
      hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
      hnumericSize hbitPositive
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxFormulaClosedFormula_alignment tokenTable
          width tokenCount current next binderArity witness).symm
        (compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph tokenTable
          width tokenCount current next binderArity witness hgraph)) <= _
  exact hparts

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphFullyFixedBounds
