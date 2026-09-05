import integration.FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax
import integration.FoundationCompactNumericListedDirectNatListListRowsDirectClosedUniformBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraphExplicitUniformResource
import integration.FoundationCompactNumericListedDirectSequentFormulaStepSuccessorCountFixedBound

/-! # Direct compiler for the complete bounded sequent-formula trace -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompiler

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsDirectUniversalUniformBound
open FoundationCompactNumericListedDirectNatListListRowsDirectClosedUniformBound
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraphExplicitUniformResource
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepSuccessorCountFixedBound
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax

def compactSequentFormulaTraceBoundedDirectNumericBound
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat) : Nat :=
  tokenTable + width + tokenCount + suffixBoundary + suffixCount +
    valueBoundary + valueCount + tableWidth + valueBound + 1

def compactSequentFormulaTraceBoundedDirectBitBound
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat) : Nat :=
  let numericBound := compactSequentFormulaTraceBoundedDirectNumericBound
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount tableWidth valueBound
  numericBound + Nat.size numericBound + 1

def compactSequentFormulaTraceBoundedDirectPayloadEnvelope
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat) : Nat :=
  let numericBound := compactSequentFormulaTraceBoundedDirectNumericBound
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount tableWidth valueBound
  let bitBound := compactSequentFormulaTraceBoundedDirectBitBound tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount
    tableWidth valueBound
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1”
  let suffixFormula := compactAdditiveNatListListRowsClosedFormula tokenTable
    width tokenCount suffixBoundary suffixCount
  let valueFormula := compactAdditiveNatListListRowsClosedFormula tokenTable
    width tokenCount valueBoundary valueCount
  let stepFormula :=
    compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueCount
      tableWidth valueBound
  compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial bitBound +
    compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
      width tokenCount suffixBoundary suffixCount numericBound bitBound +
    compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
      width tokenCount valueBoundary valueCount numericBound bitBound +
    compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueCount tableWidth valueBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ valueFormula
      stepFormula +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ suffixFormula
      (valueFormula ⋏ stepFormula) +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ countFormula
      (suffixFormula ⋏ (valueFormula ⋏ stepFormula))

noncomputable def compileCompactSequentFormulaTraceBoundedDirectClosed
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat)
    (hgraph : CompactSequentFormulaTraceBoundedGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      tableWidth valueBound) :
    CertifiedPAContextProof ∅
      (compactSequentFormulaTraceBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        tableWidth valueBound) := by
  let numericBound := compactSequentFormulaTraceBoundedDirectNumericBound
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount tableWidth valueBound
  let bitBound := compactSequentFormulaTraceBoundedDirectBitBound tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount
    tableWidth valueBound
  have hwidth : width <= numericBound := by
    unfold numericBound compactSequentFormulaTraceBoundedDirectNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound compactSequentFormulaTraceBoundedDirectNumericBound
    omega
  have hsuffixCount : suffixCount <= numericBound := by
    unfold numericBound compactSequentFormulaTraceBoundedDirectNumericBound
    omega
  have hvalueCount : valueCount <= numericBound := by
    unfold numericBound compactSequentFormulaTraceBoundedDirectNumericBound
    omega
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound compactSequentFormulaTraceBoundedDirectNumericBound
    omega
  have hsuffixBoundary : suffixBoundary <= numericBound := by
    unfold numericBound compactSequentFormulaTraceBoundedDirectNumericBound
    omega
  have hvalueBoundary : valueBoundary <= numericBound := by
    unfold numericBound compactSequentFormulaTraceBoundedDirectNumericBound
    omega
  have hnumericSize : Nat.size numericBound <= bitBound := by
    change Nat.size numericBound <=
      numericBound + Nat.size numericBound + 1
    omega
  have htokenTableSize : Nat.size tokenTable <= bitBound :=
    (Nat.size_le_size htokenTable).trans hnumericSize
  have hsuffixBoundarySize : Nat.size suffixBoundary <= bitBound :=
    (Nat.size_le_size hsuffixBoundary).trans hnumericSize
  have hvalueBoundarySize : Nat.size valueBoundary <= bitBound :=
    (Nat.size_le_size hvalueBoundary).trans hnumericSize
  let countProof :=
    (compactSequentFormulaStepSuccessorCountPublicBound suffixCount valueCount
      hgraph.1).proof
  let suffixProof :=
    compileCompactAdditiveNatListListRowsDirectUniformClosed tokenTable width
      tokenCount suffixBoundary suffixCount numericBound bitBound hgraph.2.1
      hsuffixCount hwidth htokenCount htokenTableSize hsuffixBoundarySize
      hnumericSize
  let valueProof :=
    compileCompactAdditiveNatListListRowsDirectUniformClosed tokenTable width
      tokenCount valueBoundary valueCount numericBound bitBound hgraph.2.2.1
      hvalueCount hwidth htokenCount htokenTableSize hvalueBoundarySize
      hnumericSize
  let stepProof :=
    compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueCount tableWidth valueBound hgraph.2.2.2
  let innerProof := CertifiedPAContextProof.conjunction valueProof stepProof
  let middleProof := CertifiedPAContextProof.conjunction suffixProof innerProof
  let outerProof := CertifiedPAContextProof.conjunction countProof middleProof
  exact CertifiedPAContextProof.cast
    (compactSequentFormulaTraceBoundedDirectClosedFormula_alignment tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      tableWidth valueBound).symm
    outerProof

#print axioms compileCompactSequentFormulaTraceBoundedDirectClosed

end FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompiler
