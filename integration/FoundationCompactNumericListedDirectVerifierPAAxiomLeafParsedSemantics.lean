import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectProofRootLeafFieldSemantics
import integration.FoundationCompactNumericListedDirectCertificateNodeLeafFieldSemantics

/-!
# Typed semantics of a parsed PA-axiom verifier leaf

The public successful parser graph determines the same context, closed
candidate sentence, and PA certificate that the leaf transition consumes.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics

open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectProofRootLeafFieldSemantics
open FoundationCompactNumericListedDirectCertificateNodeLeafFieldSemantics

theorem CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_pa_leaf_fields
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
      gammaBoundarySize)
    (hproofTag : proofTag = 1) :
    exists proofInput : List Nat,
    exists root : CompactNumericVerifierTask,
    exists candidate : LO.FirstOrder.ArithmeticSentence,
    exists certificate : PAAxiomCertificate,
    exists certificateInput axiomTokens certificateSuffix : List Nat,
      CompactAdditiveNatListDirectLayout
        proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish proofInput ∧
      CompactNumericVerifierTaskDirectLayout
        proofTable proofWidth proofTokenCount rootStart rootFinish root ∧
      compactListedProofNodeFieldsParser proofInput = some root ∧
      root.1 = 1 ∧
      CompactAdditiveNatListListDirectLayout
        proofTable proofWidth proofTokenCount
          (rootStart + 1) gammaFinish root.2.1 ∧
      CompactAdditiveNatListDirectLayout
        proofTable proofWidth proofTokenCount gammaFinish firstFinish
          (compactSentenceTokens candidate) ∧
      root.2.2.1 = compactSentenceTokens candidate ∧
      CompactAdditiveNatListDirectLayout
        certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish certificateInput ∧
      CompactAdditiveNatListDirectLayout
        certificateTable certificateWidth certificateTokenCount
          axiomStart axiomFinish axiomTokens ∧
      CompactAdditiveNatListDirectLayout
        certificateTable certificateWidth certificateTokenCount
          suffixStart suffixFinish certificateSuffix ∧
      compactStructuralCertificateNodeParser certificateInput =
        some (1, (axiomTokens, certificateSuffix)) ∧
      axiomTokens = compactPAAxiomCertificateTokens certificate ∧
      certificateTag = 1 := by
  have hsuccess := hgraph.1
  have hcore := hgraph.2
  rcases hsuccess.2.2.1.sound with
    ⟨proofInput, parsedRoot, hproofInput, hparsedRoot,
      hproofParser, hparsedTag⟩
  have hrootTag : parsedRoot.1 = 1 := hparsedTag.trans hproofTag
  rcases compactListedProofNodeFieldsParser_tag_one_firstFormula
      hproofParser hrootTag with
    ⟨candidate, hcandidate⟩
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hcore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaLength, hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength, _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hrealizedRootEq : realizedRoot = parsedRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore hparsedRoot hrealizedRoot
  subst realizedRoot
  have hcoreSaved := hcore
  rcases hcoreSaved with
    ⟨_hrootTagCell, hgammaStructureRaw, _hgammaRowsRaw,
      hgammaSizeEqRaw, hgammaSizeRaw,
      _hfirstSlice, _hsecondSlice, _hwitnessSlice, _hsuffixSlice⟩
  have hgammaLength' : parsedRoot.2.1.length = gammaCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaLength
  have hgammaStructure : CompactAdditiveStructuredListLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) parsedRoot.2.1.length gammaFinish gammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf, hgammaLength'] using
      hgammaStructureRaw
  have hgammaSizeEq : gammaBoundarySize = Nat.size gammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeEqRaw
  have hgammaSize :
      gammaBoundarySize ≤ (gammaCount + 1) * proofTokenCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeRaw
  have hgammaBoundaryBound : Nat.size gammaBoundary ≤
      (parsedRoot.2.1.length + 1) * proofTokenCount := by
    rw [hgammaLength', ← hgammaSizeEq]
    exact hgammaSize
  have hgammaLayout : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) gammaFinish parsedRoot.2.1 :=
    ⟨gammaBoundary, hgammaStructure, hgammaRows, hgammaBoundaryBound⟩
  have hcandidateLayout : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount gammaFinish firstFinish
        (compactSentenceTokens candidate) := by
    simpa [hcandidate, compactNumericVerifierTaskRowCoordinatesOf] using
      hfirstLayout
  have hcertificateTag : certificateTag = 1 := by
    have htagMatch := hsuccess.2.2.2.2
    rw [hproofTag] at htagMatch
    simpa [CompactNumericNodeTransitionTagMatch] using htagMatch
  have hcertificateGraph :
      FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula.CompactCertificateNodeSuccessBoundedGraph
        certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish 1 certificateEndpointBound := by
    simpa [hcertificateTag] using hsuccess.2.2.2.1
  rcases
      FoundationCompactNumericListedDirectCertificateNodeLeafFieldSemantics.CompactCertificateNodeSuccessBoundedGraph.sound_tag_one_certificate
        hcertificateGraph with
    ⟨certificate, certificateInput, axiomTokens, certificateSuffix,
      hcertificateInput, haxiom, hcertificateSuffix,
      hcertificateParser, hcertificate⟩
  exact ⟨proofInput, parsedRoot, candidate, certificate,
    certificateInput, axiomTokens, certificateSuffix,
    hproofInput, hparsedRoot, hproofParser, hrootTag,
    hgammaLayout, hcandidateLayout, hcandidate,
    hcertificateInput, haxiom, hcertificateSuffix,
    hcertificateParser, hcertificate, hcertificateTag⟩

#print axioms CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_pa_leaf_fields

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics
