import integration.FoundationCompactNumericListedNodeFields
import integration.FoundationCompactCertificateTokenMachineInversion
import integration.FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula

/-!
# Semantic fields of successfully parsed leaf certificates

A tag-one structural-certificate node carries the exact canonical token list
of a genuine PA-axiom certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeLeafFieldSemantics

open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula

theorem compactStructuralCertificateNodeParser_tag_one_axiomTokens
    {input : List Nat} {node : CompactNumericCertificateNode}
    (hparser : compactStructuralCertificateNodeParser input = some node)
    (htag : node.1 = 1) :
    exists certificate : PAAxiomCertificate,
      node.2.1 = compactPAAxiomCertificateTokens certificate := by
  cases input with
  | nil =>
      simp [compactStructuralCertificateNodeParser] at hparser
  | cons inputTag body =>
      have hinputTag : inputTag = 1 := by
        by_cases hzero : inputTag = 0
        · subst inputTag
          have hnode : (0, (([] : List Nat), body)) = node := by
            simpa [compactStructuralCertificateNodeParser] using hparser
          rw [← hnode] at htag
          simp at htag
        by_cases hone : inputTag = 1
        · exact hone
        by_cases htwo : inputTag = 2
        · subst inputTag
          have hnode : (2, (([] : List Nat), body)) = node := by
            simp [compactStructuralCertificateNodeParser] at hparser
            exact hparser
          rw [← hnode] at htag
          simp at htag
        by_cases hthree : inputTag = 3
        · subst inputTag
          have hnode : (3, (([] : List Nat), body)) = node := by
            simp [compactStructuralCertificateNodeParser] at hparser
            exact hparser
          rw [← hnode] at htag
          simp at htag
        simp [compactStructuralCertificateNodeParser, hzero, hone,
          htwo, hthree] at hparser
      subst inputTag
      cases hcertificateParser :
          compactPAAxiomCertificateTokenParser body with
      | none =>
          simp [compactStructuralCertificateNodeParser,
            hcertificateParser] at hparser
      | some suffix =>
          have hnode :
              (1, (consumedTokenPrefix body suffix, suffix)) = node := by
            simpa [compactStructuralCertificateNodeParser,
              hcertificateParser] using hparser
          rcases (compactPAAxiomCertificateTokenParser_success_iff
              body suffix).mp hcertificateParser with
            ⟨certificate, hbody⟩
          refine ⟨certificate, ?_⟩
          rw [← hnode]
          simp [hbody]

theorem CompactCertificateNodeSuccessBoundedGraph.sound_tag_one
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish endpointBound : Nat}
    (hgraph : CompactCertificateNodeSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish 1 endpointBound) :
    exists input axiomTokens suffix : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      compactStructuralCertificateNodeParser input =
        some (1, (axiomTokens, suffix)) := by
  rcases hgraph with hsimple | hfixed | hsymbol | hinduction
  · rcases hsimple with
      ⟨_inputBoundary, _hinputBoundary,
        _inputCount, _hinputCount,
        _inputBoundarySize, _hinputBoundarySize,
        _suffixBoundary, _hsuffixBoundary,
        _suffixCount, _hsuffixCount,
        _suffixBoundarySize, _hsuffixBoundarySize, hsimple⟩
    rcases hsimple.2.2.1 with hzero | htwo | hthree <;> omega
  · exact hfixed.sound
  · exact hsymbol.sound
  · exact hinduction.sound

theorem CompactCertificateNodeSuccessBoundedGraph.sound_tag_one_certificate
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish endpointBound : Nat}
    (hgraph : CompactCertificateNodeSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish 1 endpointBound) :
    exists certificate : PAAxiomCertificate,
    exists input axiomTokens suffix : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      compactStructuralCertificateNodeParser input =
        some (1, (axiomTokens, suffix)) ∧
      axiomTokens = compactPAAxiomCertificateTokens certificate := by
  rcases CompactCertificateNodeSuccessBoundedGraph.sound_tag_one hgraph with
    ⟨input, axiomTokens, suffix, hinput, haxiom, hsuffix, hparser⟩
  rcases compactStructuralCertificateNodeParser_tag_one_axiomTokens
      hparser rfl with
    ⟨certificate, hcertificate⟩
  exact ⟨certificate, input, axiomTokens, suffix,
    hinput, haxiom, hsuffix, hparser, hcertificate⟩

#print axioms compactStructuralCertificateNodeParser_tag_one_axiomTokens
#print axioms CompactCertificateNodeSuccessBoundedGraph.sound_tag_one
#print axioms CompactCertificateNodeSuccessBoundedGraph.sound_tag_one_certificate

end FoundationCompactNumericListedDirectCertificateNodeLeafFieldSemantics
