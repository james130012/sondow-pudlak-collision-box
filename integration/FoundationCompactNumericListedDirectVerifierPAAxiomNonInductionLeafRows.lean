import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
import integration.FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
import integration.FoundationCompactCertificateTokenMachineInversion
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Joint non-induction PA-axiom leaf rows

The fixed and symbol-certificate endpoint graphs are joined directly to the
rule check.  Hence the PA tag, arity, and symbol code used by the checker are
the values decoded from the same certificate slice, not independent witnesses.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomNonInductionLeafRows

open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAppendSlices

def CompactNumericVerifierPAAxiomNonInductionLeafRows
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish
      proofTag certificateTag gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount resultBoolValue : Nat)
    (fixedCoordinates : CompactCertificateNodeFixedPAEndpointCoordinates)
    (symbolCoordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    Prop :=
  proofTag = 1 ∧
    ((CompactCertificateNodeFixedPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          fixedCoordinates ∧
        CompactAdditiveFixedPAAxiomRuleCheck
          tokenTable width tokenCount gammaBoundary gammaCount
          candidateStart candidateFinish candidateCount
          fixedCoordinates.paTag 0 0 resultBoolValue) ∨
      (CompactCertificateNodeSymbolPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          symbolCoordinates ∧
        CompactAdditiveFixedPAAxiomRuleCheck
          tokenTable width tokenCount gammaBoundary gammaCount
          candidateStart candidateFinish candidateCount
          symbolCoordinates.paTag symbolCoordinates.arity
          symbolCoordinates.symbolCode resultBoolValue))

def compactPAAxiomFixedEndpointLift :
    LO.FirstOrder.ArithmeticSemisentence 49 :=
  compactCertificateNodeFixedPAEndpointGraphDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #3, #4, #5, #6, #7, #8,
      #10, #17, #18, #19, #20, #21, #22, #23, #24, #25, #26, #27,
      #28, #29, #30, #31]

def compactPAAxiomSymbolEndpointLift :
    LO.FirstOrder.ArithmeticSemisentence 49 :=
  compactCertificateNodeSymbolPAEndpointGraphDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #3, #4, #5, #6, #7, #8,
      #10, #32, #33, #34, #35, #36, #37, #38, #39, #40, #41, #42,
      #43, #44, #45, #46, #47, #48]

def compactPAAxiomFixedRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 49 :=
  compactAdditiveFixedPAAxiomRuleCheckDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #11, #12, #13, #14,
      #15, #31, ‘0’, ‘0’, #16]

def compactPAAxiomSymbolRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 49 :=
  compactAdditiveFixedPAAxiomRuleCheckDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #11, #12, #13, #14,
      #15, #46, #47, #48, #16]

def compactNumericVerifierPAAxiomNonInductionLeafRowsDef :
    𝚺₀.Semisentence 49 := .mkSigma
  (“(#9 = 1)” ⋏
    ((compactPAAxiomFixedEndpointLift ⋏ compactPAAxiomFixedRuleLift) ⋎
      (compactPAAxiomSymbolEndpointLift ⋏ compactPAAxiomSymbolRuleLift)))
  (by
    simp [compactPAAxiomFixedEndpointLift,
      compactPAAxiomSymbolEndpointLift,
      compactPAAxiomFixedRuleLift, compactPAAxiomSymbolRuleLift])

def compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish
      proofTag certificateTag gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount resultBoolValue : Nat)
    (fixedCoordinates : CompactCertificateNodeFixedPAEndpointCoordinates)
    (symbolCoordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    Fin 49 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, suffixStart, suffixFinish,
    proofTag, certificateTag, gammaBoundary, gammaCount,
    candidateStart, candidateFinish, candidateCount, resultBoolValue,
    fixedCoordinates.inputBoundary, fixedCoordinates.inputCount,
    fixedCoordinates.inputBoundarySize, fixedCoordinates.tailStart,
    fixedCoordinates.tailFinish, fixedCoordinates.tailBoundary,
    fixedCoordinates.tailCount, fixedCoordinates.tailBoundarySize,
    fixedCoordinates.axiomBoundary, fixedCoordinates.axiomCount,
    fixedCoordinates.axiomBoundarySize, fixedCoordinates.suffixBoundary,
    fixedCoordinates.suffixCount, fixedCoordinates.suffixBoundarySize,
    fixedCoordinates.paTag,
    symbolCoordinates.inputBoundary, symbolCoordinates.inputCount,
    symbolCoordinates.inputBoundarySize, symbolCoordinates.tailStart,
    symbolCoordinates.tailFinish, symbolCoordinates.tailBoundary,
    symbolCoordinates.tailCount, symbolCoordinates.tailBoundarySize,
    symbolCoordinates.axiomBoundary, symbolCoordinates.axiomCount,
    symbolCoordinates.axiomBoundarySize, symbolCoordinates.suffixBoundary,
    symbolCoordinates.suffixCount, symbolCoordinates.suffixBoundarySize,
    symbolCoordinates.paTag, symbolCoordinates.arity,
    symbolCoordinates.symbolCode]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
@[simp] theorem compactNumericVerifierPAAxiomNonInductionLeafRowsDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish
      proofTag certificateTag gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount resultBoolValue : Nat)
    (fixedCoordinates : CompactCertificateNodeFixedPAEndpointCoordinates)
    (symbolCoordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    compactNumericVerifierPAAxiomNonInductionLeafRowsDef.val.Evalb
        (compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish
          proofTag certificateTag gammaBoundary gammaCount
          candidateStart candidateFinish candidateCount resultBoolValue
          fixedCoordinates symbolCoordinates) ↔
      CompactNumericVerifierPAAxiomNonInductionLeafRows
        tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish
        proofTag certificateTag gammaBoundary gammaCount
        candidateStart candidateFinish candidateCount resultBoolValue
        fixedCoordinates symbolCoordinates := by
  let env := compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment
    tokenTable width tokenCount inputStart inputFinish
    axiomStart axiomFinish suffixStart suffixFinish
    proofTag certificateTag gammaBoundary gammaCount
    candidateStart candidateFinish candidateCount resultBoolValue
    fixedCoordinates symbolCoordinates
  change compactNumericVerifierPAAxiomNonInductionLeafRowsDef.val.Evalb env ↔ _
  have hfixedEndpointEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #3, #4, #5, #6, #7,
          #8, #10, #17, #18, #19, #20, #21, #22, #23, #24, #25, #26,
          #27, #28, #29, #30, #31]) =
        compactCertificateNodeFixedPAEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          fixedCoordinates := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env,
        compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment,
        compactCertificateNodeFixedPAEndpointEnvironment]
  have hsymbolEndpointEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #3, #4, #5, #6, #7,
          #8, #10, #32, #33, #34, #35, #36, #37, #38, #39, #40, #41,
          #42, #43, #44, #45, #46, #47, #48]) =
        compactCertificateNodeSymbolPAEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          symbolCoordinates := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env,
        compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment,
        compactCertificateNodeSymbolPAEndpointEnvironment]
  have hfixedRuleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #11, #12, #13,
          #14, #15, #31, ‘0’, ‘0’, #16]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          candidateStart, candidateFinish, candidateCount,
          fixedCoordinates.paTag, 0, 0, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment]
  have hsymbolRuleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 49), #1, #2, #11, #12, #13,
          #14, #15, #46, #47, #48, #16]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          candidateStart, candidateFinish, candidateCount,
          symbolCoordinates.paTag, symbolCoordinates.arity,
          symbolCoordinates.symbolCode, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env,
        compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment]
  have hproofTag : env 9 = proofTag := by
    simp [env,
      compactNumericVerifierPAAxiomNonInductionLeafRowsEnvironment]
  simp [compactNumericVerifierPAAxiomNonInductionLeafRowsDef,
    compactPAAxiomFixedEndpointLift, compactPAAxiomSymbolEndpointLift,
    compactPAAxiomFixedRuleLift, compactPAAxiomSymbolRuleLift,
    CompactNumericVerifierPAAxiomNonInductionLeafRows,
    hfixedEndpointEnv, hsymbolEndpointEnv,
    hfixedRuleEnv, hsymbolRuleEnv, hproofTag]

theorem compactNumericVerifierPAAxiomNonInductionLeafRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierPAAxiomNonInductionLeafRowsDef.val := by
  exact compactNumericVerifierPAAxiomNonInductionLeafRowsDef.sigma_prop

theorem CompactCertificateNodeFixedPAEndpointGraph.axiom_layout_exact
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeFixedPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeFixedPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      coordinates) :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount axiomStart axiomFinish
      [coordinates.paTag] := by
  rcases hgraph with
    ⟨_hinputRows, htailRows, haxiomRows, hsuffixRows,
      _hcertificateTag, _hfixed, _houterCons, hinnerCons, happend⟩
  rcases htailRows.realize with
    ⟨tail, htailCount, htailLayout, htailElementRows⟩
  rcases haxiomRows.realize with
    ⟨axiomTokens, haxiomCount, haxiomLayout, _haxiomElementRows⟩
  rcases hsuffixRows.realize with
    ⟨suffix, hsuffixCount, hsuffixLayout, hsuffixElementRows⟩
  have hinnerCons' :
      FoundationCompactNumericListedDirectNatListConsRows.CompactAdditiveNatListConsRows
        tokenTable width tokenCount coordinates.suffixBoundary suffix.length
        coordinates.tailBoundary tail.length coordinates.paTag := by
    simpa only [htailCount, hsuffixCount] using hinnerCons
  have htailCons : tail = coordinates.paTag :: suffix :=
    hinnerCons'.eq_cons_of_rows hsuffixElementRows htailElementRows
  have happend' :
      FoundationCompactNumericListedDirectNatListAppendSlices.CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens.length
        suffixStart suffixFinish suffix.length coordinates.tailStart
        coordinates.tailFinish tail.length := by
    simpa only [haxiomCount, hsuffixCount, htailCount] using happend
  have htailAppend : tail = axiomTokens ++ suffix :=
    (compactAdditiveNatListAppendSlices_iff_append
      haxiomLayout hsuffixLayout htailLayout).mp happend'
  have haxiomAppend : axiomTokens ++ suffix =
      [coordinates.paTag] ++ suffix := by
    rw [← htailAppend]
    simpa using htailCons
  have haxiom : axiomTokens = [coordinates.paTag] :=
    List.append_cancel_right haxiomAppend
  subst axiomTokens
  exact haxiomLayout

theorem CompactCertificateNodeSymbolPAEndpointGraph.axiom_layout_exact
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeSymbolPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      coordinates) :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount axiomStart axiomFinish
      [coordinates.paTag, coordinates.arity, coordinates.symbolCode] := by
  rcases hgraph with
    ⟨_hinputRows, _htailRows, haxiomRows, _hsuffixRows,
      _hcertificateTag, haxiomCount, _hvalid, _houterCons, _happend,
      hatZero, hatOne, hatTwo⟩
  rcases haxiomRows.realize with
    ⟨axiomTokens, haxiomCount', haxiomLayout, haxiomElementRows⟩
  have hlength : axiomTokens.length = 3 := by omega
  have hzero : axiomTokens.getI 0 = coordinates.paTag :=
    ((compactAdditiveNatListAtRows_iff_getI haxiomElementRows
      0 coordinates.paTag).mp
      (by simpa only [haxiomCount'] using hatZero)).2
  have hone : axiomTokens.getI 1 = coordinates.arity :=
    ((compactAdditiveNatListAtRows_iff_getI haxiomElementRows
      1 coordinates.arity).mp
      (by simpa only [haxiomCount'] using hatOne)).2
  have htwo : axiomTokens.getI 2 = coordinates.symbolCode :=
    ((compactAdditiveNatListAtRows_iff_getI haxiomElementRows
      2 coordinates.symbolCode).mp
      (by simpa only [haxiomCount'] using hatTwo)).2
  have haxiom : axiomTokens =
      [coordinates.paTag, coordinates.arity, coordinates.symbolCode] := by
    cases axiomTokens with
    | nil => simp at hlength
    | cons first rest =>
        cases rest with
        | nil => simp at hlength
        | cons second rest =>
            cases rest with
            | nil => simp at hlength
            | cons third rest =>
                have hrest : rest = [] :=
                  List.eq_nil_of_length_eq_zero (by simpa using hlength)
                subst rest
                simp at hzero hone htwo
                simp_all
  subst axiomTokens
  exact haxiomLayout

theorem CompactNumericVerifierPAAxiomNonInductionLeafRows.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish
      proofTag certificateTag gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount resultBoolValue : Nat}
    {fixedCoordinates : CompactCertificateNodeFixedPAEndpointCoordinates}
    {symbolCoordinates : CompactCertificateNodeSymbolPAEndpointCoordinates}
    {Gamma : List (List Nat)}
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      gammaBoundary Gamma)
    (hCandidate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateStart candidateFinish
      (compactSentenceTokens candidate))
    (hGammaCount : gammaCount = Gamma.length)
    (hCandidateCount :
      candidateCount = (compactSentenceTokens candidate).length)
    (hrows : CompactNumericVerifierPAAxiomNonInductionLeafRows
      tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish
      proofTag certificateTag gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount resultBoolValue
      fixedCoordinates symbolCoordinates) :
    ∃ input axiomTokens suffix : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, (axiomTokens, suffix)) ∧
      resultBoolValue = compactAdditiveBoolTag
        (FoundationCompactNumericListedRuleChecks.compactAxmRuleCheck
          (Gamma, (compactSentenceTokens candidate, axiomTokens))) := by
  rcases hrows with ⟨_hproofTag, hfixed | hsymbol⟩
  · rcases hfixed with ⟨hendpoint, hcheck⟩
    have hknown :=
      CompactCertificateNodeFixedPAEndpointGraph.axiom_layout_exact hendpoint
    rcases hendpoint.sound with
      ⟨input, axiomTokens, suffix,
        hinput, haxiom, hsuffix, hparser⟩
    have haxiomEq : axiomTokens = [fixedCoordinates.paTag] :=
      (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        haxiom hknown).1.symm
    subst axiomTokens
    rcases hendpoint with
      ⟨_, _, _, _, _, hfixedTag, _, _, _⟩
    have hpaParser := compactPAAxiomCertificateTokenParser_fixed
      fixedCoordinates.paTag [] hfixedTag
    rcases (compactPAAxiomCertificateTokenParser_success_iff
        [fixedCoordinates.paTag] []).mp hpaParser with
      ⟨certificate, hcertificateTokens⟩
    have hcertificateTokens' :
        compactPAAxiomCertificateTokens certificate =
          [fixedCoordinates.paTag] := by
      simpa using hcertificateTokens.symm
    have hfixedCertificate : FixedPAAxiomCertificate certificate := by
      cases certificate <;>
        simp_all [FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, CompactFixedPAAxiomTag]
    have hcheck' : CompactAdditiveFixedPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary Gamma.length
        candidateStart candidateFinish
        (compactSentenceTokens candidate).length
        (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate))
        resultBoolValue := by
      simpa [hGammaCount, hCandidateCount, hcertificateTokens',
        compactTokenAt] using hcheck
    have hresult :=
      (compactAdditiveFixedPAAxiomRuleCheck_canonical_iff
        candidate certificate hfixedCertificate hGamma hCandidate).mp hcheck'
    refine ⟨input, [fixedCoordinates.paTag], suffix,
      hinput, hknown, hsuffix, ?_, ?_⟩
    · simpa using hparser
    · simpa [hcertificateTokens'] using hresult
  · rcases hsymbol with ⟨hendpoint, hcheck⟩
    have hknown :=
      CompactCertificateNodeSymbolPAEndpointGraph.axiom_layout_exact hendpoint
    rcases hendpoint.sound with
      ⟨input, axiomTokens, suffix,
        hinput, haxiom, hsuffix, hparser⟩
    have haxiomEq : axiomTokens =
        [symbolCoordinates.paTag, symbolCoordinates.arity,
          symbolCoordinates.symbolCode] :=
      (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        haxiom hknown).1.symm
    subst axiomTokens
    rcases hendpoint with
      ⟨_, _, _, _, _, _, hvalid, _, _, _, _, _⟩
    have hpaParser := compactPAAxiomCertificateTokenParser_symbol
      symbolCoordinates.paTag symbolCoordinates.arity
      symbolCoordinates.symbolCode [] hvalid
    rcases (compactPAAxiomCertificateTokenParser_success_iff
        [symbolCoordinates.paTag, symbolCoordinates.arity,
          symbolCoordinates.symbolCode] []).mp hpaParser with
      ⟨certificate, hcertificateTokens⟩
    have hcertificateTokens' :
        compactPAAxiomCertificateTokens certificate =
          [symbolCoordinates.paTag, symbolCoordinates.arity,
            symbolCoordinates.symbolCode] := by
      simpa using hcertificateTokens.symm
    have hfixedCertificate : FixedPAAxiomCertificate certificate := by
      cases certificate <;>
        simp_all [FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, CompactSymbolPAAxiomTagValid]
    have hcheck' : CompactAdditiveFixedPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary Gamma.length
        candidateStart candidateFinish
        (compactSentenceTokens candidate).length
        (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate))
        resultBoolValue := by
      simpa [hGammaCount, hCandidateCount, hcertificateTokens',
        compactTokenAt] using hcheck
    have hresult :=
      (compactAdditiveFixedPAAxiomRuleCheck_canonical_iff
        candidate certificate hfixedCertificate hGamma hCandidate).mp hcheck'
    refine ⟨input,
      [symbolCoordinates.paTag, symbolCoordinates.arity,
        symbolCoordinates.symbolCode], suffix,
      hinput, hknown, hsuffix, ?_, ?_⟩
    · simpa using hparser
    · simpa [hcertificateTokens'] using hresult

#print axioms compactNumericVerifierPAAxiomNonInductionLeafRowsDef_spec
#print axioms compactNumericVerifierPAAxiomNonInductionLeafRowsDef_sigmaZero
#print axioms CompactNumericVerifierPAAxiomNonInductionLeafRows.sound

end FoundationCompactNumericListedDirectVerifierPAAxiomNonInductionLeafRows
