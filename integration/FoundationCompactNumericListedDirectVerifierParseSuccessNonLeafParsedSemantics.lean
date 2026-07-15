import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula

/-!
# Parsed fields for successful non-leaf verifier roots

This packages the parser objects and suffix layouts exposed by a successful
parse-payload graph when its proof tag is non-leaf.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula

theorem CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_nonleaf_fields
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize : Nat}
    (hgraph : CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize) :
    ∃ proofInput : List Nat, ∃ proofNode : CompactNumericVerifierTask,
    ∃ certificateInput : List Nat,
    ∃ certificateNode : CompactNumericCertificateNode,
    ∃ proofSuffix certificateSuffix : List Nat,
      CompactAdditiveNatListDirectLayout
        proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish proofInput ∧
      CompactNumericVerifierTaskDirectLayout
        proofTable proofWidth proofTokenCount rootStart rootFinish proofNode ∧
      compactListedProofNodeFieldsParser proofInput = some proofNode ∧
      proofNode.1 = proofTag ∧
      CompactAdditiveNatListDirectLayout
        proofTable proofWidth proofTokenCount
          witnessFinish rootFinish proofSuffix ∧
      proofSuffix = proofNode.2.2.2.2.2 ∧
      CompactAdditiveNatListDirectLayout
        certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish certificateInput ∧
      CompactAdditiveNatListDirectLayout
        certificateTable certificateWidth certificateTokenCount
          suffixStart suffixFinish certificateSuffix ∧
      compactStructuralCertificateNodeParser certificateInput = some certificateNode ∧
      certificateNode.1 = certificateTag ∧
      certificateSuffix = certificateNode.2.2 := by
  rcases hgraph.1.2.2.1.sound with
    ⟨proofInput, proofNode, hproofInput, hproofNode, hproofParser,
      hproofNodeTag⟩
  have hcore := hgraph.2
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hcore with
    ⟨realizedNode, hrealizedNode, _hrealizedNodeTag, _hgammaRows,
      _hgammaLength, _hfirst, _hfirstLength, _hsecond, _hsecondLength,
      _hwitness, _hwitnessLength, hproofSuffix, _hproofSuffixLength⟩
  have hrealizedNodeEq : realizedNode = proofNode :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore hproofNode hrealizedNode
  subst realizedNode
  have hproofSuffix' : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish
        proofNode.2.2.2.2.2 := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hproofSuffix
  rcases hgraph.1.2.2.2.1.sound with
    ⟨certificateInput, certificateSuffix, hcertificateInput,
      hcertificateSuffix, hcertificateParser⟩ |
    ⟨certificateInput, _axiomTokens, certificateSuffix,
      hcertificateInput, _haxiom, hcertificateSuffix,
      hcertificateParser⟩
  · exact ⟨proofInput, proofNode, certificateInput,
      (certificateTag, ([], certificateSuffix)),
      proofNode.2.2.2.2.2, certificateSuffix,
      hproofInput, hproofNode, hproofParser, hproofNodeTag,
      hproofSuffix', rfl, hcertificateInput, hcertificateSuffix,
      hcertificateParser, rfl, rfl⟩
  · exact ⟨proofInput, proofNode, certificateInput,
      (certificateTag, (_axiomTokens, certificateSuffix)),
      proofNode.2.2.2.2.2, certificateSuffix,
      hproofInput, hproofNode, hproofParser, hproofNodeTag,
      hproofSuffix', rfl, hcertificateInput, hcertificateSuffix,
      hcertificateParser, rfl, rfl⟩

#print axioms CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_nonleaf_fields

end FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
