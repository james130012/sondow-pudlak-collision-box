import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafBounds

/-! # Five-leaf payload bound for one natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPartsPayloadBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafTypes
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds

theorem compactAdditiveNatListConsRowsTailPartsCertificate_payload_le_fullyFixed
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat)
    (facts : NatListConsRowsTailFixedFacts data numericBound bitBound)
    (leaves : NatListConsRowsTailLeafBounds data numericBound bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailPartsCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary index data) <=
      natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let valuation := consRowsTailValuation index
  let formula1 := consRowsTailSourceLeftFormula tokenTable width tokenCount
    sourceBoundary targetBoundary index data
  let formula2 := consRowsTailSourceRightFormula tokenTable width tokenCount
    sourceBoundary targetBoundary index data
  let formula3 := consRowsTailTargetLeftFormula tokenTable width tokenCount
    sourceBoundary targetBoundary index data
  let formula4 := consRowsTailTargetRightFormula tokenTable width tokenCount
    sourceBoundary targetBoundary index data
  let formula5 := consRowsTailAtomicRowFormula tokenTable width tokenCount
    sourceBoundary targetBoundary index data
  let entryResource :=
    natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    natListConsRowsTailTerminalAssemblySyntaxPolynomial numericBound bitBound
  have hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))))).length <=
        syntaxResource := by
    exact fiveFormulaCode_le_natListConsRowsTailTerminalAssembly formula1
      formula2 formula3 formula4 formula5 numericBound bitBound
      (by simpa only [formula1, entryResource] using leaves.sourceLeftCode)
      (by simpa only [formula2, entryResource] using leaves.sourceRightCode)
      (by simpa only [formula3, entryResource] using leaves.targetLeftCode)
      (by simpa only [formula4, entryResource] using leaves.targetRightCode)
      (by simpa only [formula5, rowResource] using leaves.atomicRowCode)
  have hvariables :
      (formula1 ⋏
        (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))).freeVariables ⊆
          {0} := by
    simpa only [formula1, formula2, formula3, formula4, formula5,
      consRowsTailPartsFormula] using
      (consRowsTailPartsFormula_freeVariables_subset_singleton data)
  have hgeneral :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_singletonGeneral
      valuation formula1 formula2 formula3 formula4 formula5 entryResource
      entryResource entryResource entryResource rowResource syntaxResource
      numericBound (by
        simpa only [syntaxResource] using
          natListConsRowsTailTerminalAssemblySyntax_positive numericBound
            bitBound)
      (by simpa only [valuation] using facts.valuation_zero_le)
      hvariables hcode (by
        simpa only [syntaxResource,
          natListConsRowsTailTerminalContextCodePolynomial] using
          natListConsRowsTailTerminalContextCode_le_assembly numericBound
            bitBound)
  have htail4 := transparentHybridConjunctionPayloadBound_le
    (consRowsTailTargetRightCertificate tokenTable width tokenCount
      sourceBoundary targetBoundary index data)
    (consRowsTailAtomicRowCertificate tokenTable width tokenCount
      sourceBoundary targetBoundary index data)
    entryResource rowResource
    (by simpa only [entryResource] using leaves.targetRightPayload)
    (by simpa only [rowResource] using leaves.atomicRowPayload)
  have htail3 := transparentHybridConjunctionPayloadBound_le
    (consRowsTailTargetLeftCertificate tokenTable width tokenCount
      sourceBoundary targetBoundary index data)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (consRowsTailTargetRightCertificate tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
      (consRowsTailAtomicRowCertificate tokenTable width tokenCount
        sourceBoundary targetBoundary index data))
    entryResource
    (transparentHybridConjunctionPayloadEnvelope valuation formula4 formula5
      entryResource rowResource)
    (by simpa only [entryResource] using leaves.targetLeftPayload)
    (by simpa only [valuation, formula4, formula5] using htail4)
  have htail2 := transparentHybridConjunctionPayloadBound_le
    (consRowsTailSourceRightCertificate tokenTable width tokenCount
      sourceBoundary targetBoundary index data)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (consRowsTailTargetLeftCertificate tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (consRowsTailTargetRightCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data)
        (consRowsTailAtomicRowCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data)))
    entryResource
    (transparentHybridConjunctionPayloadEnvelope valuation formula3
      (formula4 ⋏ formula5) entryResource
      (transparentHybridConjunctionPayloadEnvelope valuation formula4 formula5
        entryResource rowResource))
    (by simpa only [entryResource] using leaves.sourceRightPayload)
    (by simpa only [valuation, formula3, formula4, formula5] using htail3)
  have htotal := transparentHybridConjunctionPayloadBound_le
    (consRowsTailSourceLeftCertificate tokenTable width tokenCount
      sourceBoundary targetBoundary index data)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (consRowsTailSourceRightCertificate tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (consRowsTailTargetLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (consRowsTailTargetRightCertificate tokenTable width tokenCount
            sourceBoundary targetBoundary index data)
          (consRowsTailAtomicRowCertificate tokenTable width tokenCount
            sourceBoundary targetBoundary index data))))
    entryResource
    (transparentHybridConjunctionPayloadEnvelope valuation formula2
      (formula3 ⋏ (formula4 ⋏ formula5)) entryResource
      (transparentHybridConjunctionPayloadEnvelope valuation formula3
        (formula4 ⋏ formula5) entryResource
        (transparentHybridConjunctionPayloadEnvelope valuation formula4
          formula5 entryResource rowResource)))
    (by simpa only [entryResource] using leaves.sourceLeftPayload)
    (by simpa only [valuation, formula2, formula3, formula4, formula5] using
      htail2)
  have hpartsCertificateEq :
      compactAdditiveNatListConsRowsTailPartsCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary index data =
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (consRowsTailSourceLeftCertificate tokenTable width tokenCount
            sourceBoundary targetBoundary index data)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (consRowsTailSourceRightCertificate tokenTable width tokenCount
              sourceBoundary targetBoundary index data)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (consRowsTailTargetLeftCertificate tokenTable width tokenCount
                sourceBoundary targetBoundary index data)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (consRowsTailTargetRightCertificate tokenTable width tokenCount
                  sourceBoundary targetBoundary index data)
                (consRowsTailAtomicRowCertificate tokenTable width tokenCount
                  sourceBoundary targetBoundary index data)))) := by
    rfl
  have hparts :
      hybridFormulaStructuralPayloadBound
          (compactAdditiveNatListConsRowsTailPartsCertificate tokenTable width
            tokenCount sourceBoundary targetBoundary index data) <=
        transparentHybridConjunctionPayloadEnvelope valuation formula1
          (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))) entryResource
          (transparentHybridConjunctionPayloadEnvelope valuation formula2
            (formula3 ⋏ (formula4 ⋏ formula5)) entryResource
            (transparentHybridConjunctionPayloadEnvelope valuation formula3
              (formula4 ⋏ formula5) entryResource
              (transparentHybridConjunctionPayloadEnvelope valuation formula4
                formula5 entryResource rowResource))) := by
    rw [hpartsCertificateEq]
    exact htotal
  unfold natListConsRowsTailTerminalFullyFixedPayloadPolynomial
  simpa only [syntaxResource, entryResource, rowResource] using
    hparts.trans hgeneral

#print axioms
  compactAdditiveNatListConsRowsTailPartsCertificate_payload_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPartsPayloadBound
