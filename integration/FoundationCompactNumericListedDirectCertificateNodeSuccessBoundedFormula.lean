import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula
import integration.FoundationCompactCertificateTokenMachineInversion

/-!
# Unified bounded success formula for structural-certificate nodes

The four exhaustive successful parser families share one public relation:
simple tags 0/2/3, fixed one-token PA tags, symbol PA tags 3/4, and induction
tag 22 with its complete formula-parser trace.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula

open FoundationCompactArithmeticSymbolCode
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactPAAxiomCertificate
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula

def CompactCertificateNodeSuccessBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) : Prop :=
  CompactCertificateNodeSimpleEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish certificateTag endpointBound ∨
    CompactCertificateNodeFixedPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish
        certificateTag endpointBound ∨
    CompactCertificateNodeSymbolPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish
        certificateTag endpointBound ∨
    CompactCertificateNodeInductionPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag endpointBound

def compactCertificateNodeSuccessBoundedGraphDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound.
    !(compactCertificateNodeSimpleEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish certificateTag endpointBound ∨
    !(compactCertificateNodeFixedPAEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish
        certificateTag endpointBound ∨
    !(compactCertificateNodeSymbolPAEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish
        certificateTag endpointBound ∨
    !(compactCertificateNodeInductionPAEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag endpointBound”

set_option maxHeartbeats 1000000 in
-- Normalizing four nested bounded endpoint formulas needs a local budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeSuccessBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    compactCertificateNodeSuccessBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag, endpointBound] ↔
      CompactCertificateNodeSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag endpointBound := by
  let env : Fin 13 → Nat :=
    ![tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, endpointBound]
  change compactCertificateNodeSuccessBoundedGraphDef.val.Evalb env ↔ _
  have hsimpleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #3, #4,
          #9, #10, #11, #12]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          suffixStart, suffixFinish, certificateTag, endpointBound] := by
    funext index
    fin_cases index <;> rfl
  have hpaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #3, #4,
          #5, #6, #9, #10, #11, #12]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          axiomStart, axiomFinish, suffixStart, suffixFinish,
          certificateTag, endpointBound] := by
    funext index
    fin_cases index <;> rfl
  have hinductionEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #3, #4,
          #5, #6, #7, #8, #9, #10, #11, #12]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag, endpointBound] := by
    funext index
    fin_cases index <;> rfl
  simp [compactCertificateNodeSuccessBoundedGraphDef,
    CompactCertificateNodeSuccessBoundedGraph,
    hsimpleEnv, hpaEnv, hinductionEnv]

theorem compactCertificateNodeSuccessBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeSuccessBoundedGraphDef.val := by
  simp [compactCertificateNodeSuccessBoundedGraphDef]

def CompactCertificateNodeSuccessSemantic
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat) :
    Prop :=
  (∃ input suffix : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, ([], suffix))) ∨
    (∃ input axiomTokens suffix : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, (axiomTokens, suffix)))

theorem CompactCertificateNodeSuccessBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat}
    (hgraph : CompactCertificateNodeSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag endpointBound) :
    CompactCertificateNodeSuccessSemantic
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag := by
  rcases hgraph with hsimple | hfixed | hsymbol | hinduction
  · rcases hsimple.sound with
      ⟨input, suffix, hinput, hsuffix, hparser⟩
    exact Or.inl ⟨input, suffix, hinput, hsuffix, hparser⟩
  · rcases hfixed.sound with
      ⟨input, axiomTokens, suffix, hinput, haxiom, hsuffix, hparser⟩
    exact Or.inr
      ⟨input, axiomTokens, suffix, hinput, haxiom, hsuffix, hparser⟩
  · rcases hsymbol.sound with
      ⟨input, axiomTokens, suffix, hinput, haxiom, hsuffix, hparser⟩
    exact Or.inr
      ⟨input, axiomTokens, suffix, hinput, haxiom, hsuffix, hparser⟩
  · rcases hinduction.sound with
      ⟨input, axiomTokens, suffix, hinput, haxiom, hsuffix, hparser⟩
    exact Or.inr
      ⟨input, axiomTokens, suffix, hinput, haxiom, hsuffix, hparser⟩

theorem exists_compactCertificateNodeSuccessBoundedGraph_of_simple
    (tag : Nat) (suffix : List Nat)
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactCertificateNodeSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish tag endpointBound := by
  have hparser :
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        (tag :: suffix) = some (tag, ([], suffix)) := by
    rcases htag with rfl | rfl | rfl <;>
      simp [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser]
  rcases exists_compactCertificateNodeSimpleEndpointBoundedGraph_of_success
      hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      suffixStart, suffixFinish, endpointBound, hsimple⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    0, 0, 0, 0, suffixStart, suffixFinish, endpointBound, Or.inl hsimple⟩

theorem exists_compactCertificateNodeSuccessBoundedGraph_of_fixedPA
    (paTag : Nat) (suffix : List Nat)
    (hfixed : CompactFixedPAAxiomTag paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactCertificateNodeSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish 1 endpointBound := by
  rcases exists_compactCertificateNodeFixedPAEndpointBoundedGraph_of_results
      paTag suffix hfixed with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, suffixStart, suffixFinish,
      endpointBound, hfixedGraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, 0, 0, suffixStart, suffixFinish,
    endpointBound, Or.inr (Or.inl hfixedGraph)⟩

theorem exists_compactCertificateNodeSuccessBoundedGraph_of_symbolPA
    (paTag arity symbolCode : Nat) (suffix : List Nat)
    (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactCertificateNodeSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish 1 endpointBound := by
  rcases exists_compactCertificateNodeSymbolPAEndpointBoundedGraph_of_results
      paTag arity symbolCode suffix hvalid with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, suffixStart, suffixFinish,
      endpointBound, hsymbolGraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, 0, 0, suffixStart, suffixFinish,
    endpointBound, Or.inr (Or.inr (Or.inl hsymbolGraph))⟩

theorem exists_compactCertificateNodeSuccessBoundedGraph_of_inductionPA
    (formulaInput suffix : List Nat)
    (hformula : FoundationCompactSyntaxTokenMachine.compactFormulaTokenParser
      1 formulaInput = some suffix) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactCertificateNodeSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish 1 endpointBound := by
  rcases exists_compactCertificateNodeInductionPAEndpointBoundedGraph_of_results
      formulaInput suffix hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, endpointBound, hinductionGraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, endpointBound,
    Or.inr (Or.inr (Or.inr hinductionGraph))⟩

/-- Every successful public structural-certificate node parse retains its exact
input layout and belongs to one of the four bounded branches. -/
theorem exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success_with_inputLayout
    {input : List Nat} {certificateTag : Nat}
    {axiomTokens suffix : List Nat}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, (axiomTokens, suffix))) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag endpointBound := by
  have simpleBranch
      {branchInput : List Nat} {tag : Nat}
      {branchAxiomTokens branchSuffix : List Nat}
      (hbranchParser :
        FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
          branchInput = some (tag, (branchAxiomTokens, branchSuffix)))
      (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
      ∃ tokenTable width tokenCount inputStart inputFinish,
      ∃ axiomStart axiomFinish formulaStart formulaFinish,
      ∃ suffixStart suffixFinish endpointBound,
        FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish branchInput ∧
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish tag endpointBound := by
    rcases
        exists_compactCertificateNodeSimpleEndpointGraph_of_success_with_inputLayout
          hbranchParser htag with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        suffixStart, suffixFinish, _coordinates, hinputLayout, hbranchRaw⟩
    rcases CompactCertificateNodeSimpleEndpointGraph.exists_bounded hbranchRaw with
      ⟨endpointBound, hbranch⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      0, 0, 0, 0, suffixStart, suffixFinish, endpointBound,
      hinputLayout, Or.inl hbranch⟩
  have fixedBranch
      (paTag : Nat) (branchSuffix : List Nat)
      (hfixed : CompactFixedPAAxiomTag paTag) :
      ∃ tokenTable width tokenCount inputStart inputFinish,
      ∃ axiomStart axiomFinish formulaStart formulaFinish,
      ∃ suffixStart suffixFinish endpointBound,
        FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish
              (1 :: paTag :: branchSuffix) ∧
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound := by
    rcases
        exists_compactCertificateNodeFixedPAEndpointGraph_of_results_with_inputLayout
          paTag branchSuffix hfixed with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, suffixStart, suffixFinish,
        _coordinates, hinputLayout, hbranchRaw⟩
    rcases CompactCertificateNodeFixedPAEndpointGraph.exists_bounded hbranchRaw with
      ⟨endpointBound, hbranch⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, 0, 0, suffixStart, suffixFinish, endpointBound,
      hinputLayout, Or.inr (Or.inl hbranch)⟩
  have symbolBranch
      (paTag arity symbolCode : Nat) (branchSuffix : List Nat)
      (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
      ∃ tokenTable width tokenCount inputStart inputFinish,
      ∃ axiomStart axiomFinish formulaStart formulaFinish,
      ∃ suffixStart suffixFinish endpointBound,
        FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish
              (1 :: paTag :: arity :: symbolCode :: branchSuffix) ∧
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound := by
    rcases
        exists_compactCertificateNodeSymbolPAEndpointGraph_of_results_with_inputLayout
          paTag arity symbolCode branchSuffix hvalid with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, suffixStart, suffixFinish,
        _coordinates, hinputLayout, hbranchRaw⟩
    rcases CompactCertificateNodeSymbolPAEndpointGraph.exists_bounded hbranchRaw with
      ⟨endpointBound, hbranch⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, 0, 0, suffixStart, suffixFinish, endpointBound,
      hinputLayout, Or.inr (Or.inr (Or.inl hbranch))⟩
  have inductionBranch
      (formulaInput branchSuffix : List Nat)
      (hformula : FoundationCompactSyntaxTokenMachine.compactFormulaTokenParser
        1 formulaInput = some branchSuffix) :
      ∃ tokenTable width tokenCount inputStart inputFinish,
      ∃ axiomStart axiomFinish formulaStart formulaFinish,
      ∃ suffixStart suffixFinish endpointBound,
        FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish
              (1 :: 22 :: formulaInput) ∧
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound := by
    rcases
        exists_compactCertificateNodeInductionPAEndpointGraph_of_results_with_inputLayout
          formulaInput branchSuffix hformula with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, _coordinates, hinputLayout, hbranchRaw⟩
    rcases CompactCertificateNodeInductionPAEndpointGraph.exists_bounded hbranchRaw with
      ⟨endpointBound, hbranch⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, endpointBound,
      hinputLayout, Or.inr (Or.inr (Or.inr hbranch))⟩
  cases input with
  | nil =>
      simp [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser]
        at hparser
  | cons tag tail =>
      by_cases h0 : tag = 0
      · subst tag
        have hparseEq :
            some (0, (([] : List Nat), tail)) =
              some (certificateTag, (axiomTokens, suffix)) := by
          simpa [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser]
            using hparser
        have hnode := Option.some.inj hparseEq
        have htag : certificateTag = 0 :=
          (congrArg (fun node => node.1) hnode).symm
        subst certificateTag
        exact simpleBranch hparser (Or.inl rfl)
      by_cases h1 : tag = 1
      · subst tag
        cases hpa : compactPAAxiomCertificateTokenParser tail with
        | none =>
            simp [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser,
              h0, hpa] at hparser
        | some after =>
            have hparseEq :
                some (1, (FoundationCompactNumericSyntaxValueParser.consumedTokenPrefix
                  tail after, after)) =
                  some (certificateTag, (axiomTokens, suffix)) := by
              simpa [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser,
                h0, hpa] using hparser
            have hnode := Option.some.inj hparseEq
            have htag : certificateTag = 1 :=
              (congrArg (fun node => node.1) hnode).symm
            subst certificateTag
            rcases (compactPAAxiomCertificateTokenParser_success_iff
                tail after).mp hpa with
              ⟨certificate, htail⟩
            rw [htail]
            cases certificate with
            | eqRefl =>
                exact fixedBranch 0 after (by simp [CompactFixedPAAxiomTag])
            | eqSymm =>
                exact fixedBranch 1 after (by simp [CompactFixedPAAxiomTag])
            | eqTrans =>
                exact fixedBranch 2 after (by simp [CompactFixedPAAxiomTag])
            | eqFuncExt functionSymbol =>
                exact symbolBranch
                  3 _ (Encodable.encode functionSymbol) after
                    (Or.inl ⟨rfl, arithmeticFuncCodeValid_encode functionSymbol⟩)
            | eqRelExt relationSymbol =>
                exact symbolBranch
                  4 _ (Encodable.encode relationSymbol) after
                    (Or.inr ⟨rfl, arithmeticRelCodeValid_encode relationSymbol⟩)
            | addZero =>
                exact fixedBranch 5 after (by simp [CompactFixedPAAxiomTag])
            | addAssoc =>
                exact fixedBranch 6 after (by simp [CompactFixedPAAxiomTag])
            | addComm =>
                exact fixedBranch 7 after (by simp [CompactFixedPAAxiomTag])
            | addEqOfLt =>
                exact fixedBranch 8 after (by simp [CompactFixedPAAxiomTag])
            | zeroLe =>
                exact fixedBranch 9 after (by simp [CompactFixedPAAxiomTag])
            | zeroLtOne =>
                exact fixedBranch 10 after (by simp [CompactFixedPAAxiomTag])
            | oneLeOfZeroLt =>
                exact fixedBranch 11 after (by simp [CompactFixedPAAxiomTag])
            | addLtAdd =>
                exact fixedBranch 12 after (by simp [CompactFixedPAAxiomTag])
            | mulZero =>
                exact fixedBranch 13 after (by simp [CompactFixedPAAxiomTag])
            | mulOne =>
                exact fixedBranch 14 after (by simp [CompactFixedPAAxiomTag])
            | mulAssoc =>
                exact fixedBranch 15 after (by simp [CompactFixedPAAxiomTag])
            | mulComm =>
                exact fixedBranch 16 after (by simp [CompactFixedPAAxiomTag])
            | mulLtMul =>
                exact fixedBranch 17 after (by simp [CompactFixedPAAxiomTag])
            | distr =>
                exact fixedBranch 18 after (by simp [CompactFixedPAAxiomTag])
            | ltIrrefl =>
                exact fixedBranch 19 after (by simp [CompactFixedPAAxiomTag])
            | ltTrans =>
                exact fixedBranch 20 after (by simp [CompactFixedPAAxiomTag])
            | ltTri =>
                exact fixedBranch 21 after (by simp [CompactFixedPAAxiomTag])
            | induction body =>
                exact inductionBranch
                  (compactArithmeticFormulaTokens body ++ after) after
                    (compactFormulaTokenParser_canonical_append body after)
      by_cases h2 : tag = 2
      · subst tag
        have hparseEq :
            some (2, (([] : List Nat), tail)) =
              some (certificateTag, (axiomTokens, suffix)) := by
          simpa [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser,
            h0, h1] using hparser
        have hnode := Option.some.inj hparseEq
        have htag : certificateTag = 2 :=
          (congrArg (fun node => node.1) hnode).symm
        subst certificateTag
        exact simpleBranch hparser (Or.inr (Or.inl rfl))
      by_cases h3 : tag = 3
      · subst tag
        have hparseEq :
            some (3, (([] : List Nat), tail)) =
              some (certificateTag, (axiomTokens, suffix)) := by
          simpa [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser,
            h0, h1, h2] using hparser
        have hnode := Option.some.inj hparseEq
        have htag : certificateTag = 3 :=
          (congrArg (fun node => node.1) hnode).symm
        subst certificateTag
        exact simpleBranch hparser (Or.inr (Or.inr rfl))
      simp [FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser,
        h0, h1, h2, h3] at hparser

/-- Compatibility wrapper that discards the exact input layout. -/
theorem exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success
    {input : List Nat} {certificateTag : Nat}
    {axiomTokens suffix : List Nat}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, (axiomTokens, suffix))) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactCertificateNodeSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag endpointBound := by
  rcases
      exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success_with_inputLayout
        hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, endpointBound, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, endpointBound, hgraph⟩

#print axioms compactCertificateNodeSuccessBoundedGraphDef_spec
#print axioms compactCertificateNodeSuccessBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeSuccessBoundedGraph.sound
#print axioms exists_compactCertificateNodeSuccessBoundedGraph_of_simple
#print axioms exists_compactCertificateNodeSuccessBoundedGraph_of_fixedPA
#print axioms exists_compactCertificateNodeSuccessBoundedGraph_of_symbolPA
#print axioms exists_compactCertificateNodeSuccessBoundedGraph_of_inductionPA
#print axioms exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success_with_inputLayout
#print axioms exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success

end FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
