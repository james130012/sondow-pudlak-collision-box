import integration.FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompiler

/-! # Public payload bound for the bounded sequent-formula trace compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompilerBounds

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
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompiler

theorem compileCompactSequentFormulaTraceBoundedDirectClosed_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount tableWidth valueBound : Nat)
    (hgraph : CompactSequentFormulaTraceBoundedGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      tableWidth valueBound) :
    (compileCompactSequentFormulaTraceBoundedDirectClosed tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      tableWidth valueBound hgraph).payloadLength <=
      compactSequentFormulaTraceBoundedDirectPayloadEnvelope tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        tableWidth valueBound := by
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
  have hsuffixCountSize : Nat.size suffixCount <= bitBound :=
    (Nat.size_le_size hsuffixCount).trans hnumericSize
  have hvalueCountSize : Nat.size valueCount <= bitBound :=
    (Nat.size_le_size hvalueCount).trans hnumericSize
  let countBound :=
    compactSequentFormulaStepSuccessorCountPublicBound suffixCount valueCount
      hgraph.1
  let countProof := countBound.proof
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
  have hcountResource : countBound.resource <=
      compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial
        bitBound := by
    exact
      compactSequentFormulaStepSuccessorCountPublicBound_resource_le_fixed
        suffixCount valueCount bitBound hsuffixCountSize hvalueCountSize
        hgraph.1
  have hcount : countProof.payloadLength <=
      compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial
        bitBound :=
    countBound.payloadLength_le.trans hcountResource
  have hsuffix : suffixProof.payloadLength <=
      compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
        width tokenCount suffixBoundary suffixCount numericBound bitBound :=
    compileCompactAdditiveNatListListRowsDirectUniformClosed_payloadLength_le
      tokenTable width tokenCount suffixBoundary suffixCount numericBound
      bitBound hgraph.2.1 hsuffixCount hwidth htokenCount htokenTableSize
      hsuffixBoundarySize hnumericSize
  have hvalue : valueProof.payloadLength <=
      compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
        width tokenCount valueBoundary valueCount numericBound bitBound :=
    compileCompactAdditiveNatListListRowsDirectUniformClosed_payloadLength_le
      tokenTable width tokenCount valueBoundary valueCount numericBound
      bitBound hgraph.2.2.1 hvalueCount hwidth htokenCount htokenTableSize
      hvalueBoundarySize hnumericSize
  have hstep : stepProof.payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount valueCount tableWidth valueBound :=
    compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext_payloadLength_le
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueCount tableWidth valueBound hgraph.2.2.2
  have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
    valueProof stepProof
  have hmiddle := CertifiedPAContextProof.conjunction_payloadLength_le
    suffixProof innerProof
  have houter := CertifiedPAContextProof.conjunction_payloadLength_le
    countProof middleProof
  have hinnerBound : innerProof.payloadLength <=
      compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
          width tokenCount valueBoundary valueCount numericBound bitBound +
        compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount valueCount tableWidth valueBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
            tokenCount valueBoundary valueCount)
          (compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable
            width tokenCount suffixBoundary suffixCount valueBoundary
            valueCount valueCount tableWidth valueBound) := by
    change (CertifiedPAContextProof.conjunction valueProof stepProof).payloadLength <= _
    exact hinner.trans (by omega)
  have hmiddleBound : middleProof.payloadLength <=
      compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
          width tokenCount suffixBoundary suffixCount numericBound bitBound +
        compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
          width tokenCount valueBoundary valueCount numericBound bitBound +
        compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount valueCount tableWidth valueBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
            tokenCount valueBoundary valueCount)
          (compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable
            width tokenCount suffixBoundary suffixCount valueBoundary
            valueCount valueCount tableWidth valueBound) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
            tokenCount suffixBoundary suffixCount)
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
              tokenCount valueBoundary valueCount ⋏
            compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable
              width tokenCount suffixBoundary suffixCount valueBoundary
              valueCount valueCount tableWidth valueBound) := by
    change
      (CertifiedPAContextProof.conjunction suffixProof innerProof).payloadLength <= _
    exact hmiddle.trans (by omega)
  have houterBound : outerProof.payloadLength <=
      compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial bitBound +
        compactAdditiveNatListListRowsDirectUniformUniversalResource
          tokenTable width tokenCount suffixBoundary suffixCount numericBound
          bitBound +
        compactAdditiveNatListListRowsDirectUniformUniversalResource
          tokenTable width tokenCount valueBoundary valueCount numericBound
          bitBound +
        compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount valueCount tableWidth valueBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
            tokenCount valueBoundary valueCount)
          (compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable
            width tokenCount suffixBoundary suffixCount valueBoundary
            valueCount valueCount tableWidth valueBound) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
            tokenCount suffixBoundary suffixCount)
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
              tokenCount valueBoundary valueCount ⋏
            compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable
              width tokenCount suffixBoundary suffixCount valueBoundary
              valueCount valueCount tableWidth valueBound) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          “!!(shortBinaryNumeralTerm suffixCount) =
            !!(shortBinaryNumeralTerm valueCount) + 1”
          (compactAdditiveNatListListRowsClosedFormula tokenTable width
              tokenCount suffixBoundary suffixCount ⋏
            (compactAdditiveNatListListRowsClosedFormula tokenTable width
                tokenCount valueBoundary valueCount ⋏
              compactSequentFormulaStepRowsBoundedDirectClosedFormula
                tokenTable width tokenCount suffixBoundary suffixCount
                valueBoundary valueCount valueCount tableWidth valueBound)) := by
    change
      (CertifiedPAContextProof.conjunction countProof middleProof).payloadLength <= _
    exact houter.trans (by omega)
  unfold compileCompactSequentFormulaTraceBoundedDirectClosed
  rw [CertifiedPAContextProof.cast_payloadLength]
  change outerProof.payloadLength <= _
  exact houterBound.trans (by
    unfold compactSequentFormulaTraceBoundedDirectPayloadEnvelope
    dsimp only [numericBound, bitBound, countBound, countProof, suffixProof,
      valueProof, stepProof, innerProof, middleProof, outerProof]
    omega)

#print axioms
  compileCompactSequentFormulaTraceBoundedDirectClosed_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompilerBounds
