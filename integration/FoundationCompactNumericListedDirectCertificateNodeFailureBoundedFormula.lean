import integration.FoundationCompactNumericListedDirectCertificateNodeFailureSemantics
import integration.FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureBoundedFormula

/-!
# Unified bounded failure formula for structural-certificate nodes

The relation is exhaustive for the public structural-certificate node parser:
outer empty/invalid dispatch, immediate PA failure, malformed symbol PA tags,
and induction-formula no-output.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectCertificateNodeFailureSemantics
open FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureBoundedFormula

def CompactCertificateNodeOuterFailureLiftedBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) : Prop :=
  ∃ tailStart, tailStart ≤ endpointBound ∧
  ∃ tailFinish, tailFinish ≤ endpointBound ∧
  ∃ outerBound, outerBound ≤ endpointBound ∧
    CompactCertificateNodeOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish outerBound

def compactCertificateNodeOuterFailureLiftedBoundedGraphDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish endpointBound.
    ∃ tailStart <⁺ endpointBound,
    ∃ tailFinish <⁺ endpointBound,
    ∃ outerBound <⁺ endpointBound,
      !(compactCertificateNodeOuterFailureEndpointBoundedGraphDef)
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish outerBound”

@[simp] theorem compactCertificateNodeOuterFailureLiftedBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactCertificateNodeOuterFailureLiftedBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish, endpointBound] ↔
      CompactCertificateNodeOuterFailureLiftedBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hrow (outerBound tailFinish tailStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![outerBound, tailFinish, tailStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0])
          Empty.elim)
        compactCertificateNodeOuterFailureEndpointBoundedGraphDef.val ↔
      CompactCertificateNodeOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish outerBound := by
    have henv :
        (Semiterm.val
            ![outerBound, tailFinish, tailStart,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              endpointBound]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0]) =
          ![tokenTable, width, tokenCount, inputStart, inputFinish,
            tailStart, tailFinish, outerBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeOuterFailureEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish outerBound
  simp [compactCertificateNodeOuterFailureLiftedBoundedGraphDef,
    CompactCertificateNodeOuterFailureLiftedBoundedGraph, hrow]

def CompactCertificateNodeFailureBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) : Prop :=
  CompactCertificateNodeOuterFailureLiftedBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound ∨
    CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound ∨
    CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound ∨
    CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound

def compactCertificateNodeFailureBoundedGraphDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish endpointBound.
    !(compactCertificateNodeOuterFailureLiftedBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish endpointBound ∨
    !(compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish endpointBound ∨
    !(compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish endpointBound ∨
    !(compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish endpointBound”

@[simp] theorem compactCertificateNodeFailureBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactCertificateNodeFailureBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish, endpointBound] ↔
      CompactCertificateNodeFailureBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have henv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, inputStart, inputFinish, endpointBound]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 6), #1, #2, #3, #4, #5]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactCertificateNodeFailureBoundedGraphDef,
    CompactCertificateNodeFailureBoundedGraph, henv]

theorem compactCertificateNodeFailureBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeFailureBoundedGraphDef.val := by
  simp [compactCertificateNodeFailureBoundedGraphDef]

theorem CompactCertificateNodeFailureBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hgraph : CompactCertificateNodeFailureBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactStructuralCertificateNodeParser input = none := by
  rcases hgraph with houter | himmediate | hsymbol | hinduction
  · rcases houter with
      ⟨_tailStart, _, _tailFinish, _, _outerBound, _, hbounded⟩
    exact hbounded.sound
  · exact himmediate.sound
  · exact hsymbol.sound
  · exact hinduction.sound

theorem exists_compactCertificateNodeFailureBoundedGraph_of_outer_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [] ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, outerBound, hinputLayout, houter⟩
  let endpointBound := tailStart + tailFinish + outerBound
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, Or.inl ?_⟩
  exact ⟨tailStart, by dsimp only [endpointBound]; omega,
    tailFinish, by dsimp only [endpointBound]; omega,
    outerBound, by dsimp only [endpointBound]; omega, houter⟩

theorem exists_compactCertificateNodeFailureBoundedGraph_of_outer_invalid_with_inputLayout
    (tag : Nat) (tail : List Nat)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) (h3 : tag ≠ 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: tail) ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_invalid_with_inputLayout
      tag tail h0 h1 h2 h3 with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, outerBound, hinputLayout, houter⟩
  let endpointBound := tailStart + tailFinish + outerBound
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, Or.inl ?_⟩
  exact ⟨tailStart, by dsimp only [endpointBound]; omega,
    tailFinish, by dsimp only [endpointBound]; omega,
    outerBound, by dsimp only [endpointBound]; omega, houter⟩

theorem exists_compactCertificateNodeFailureBoundedGraph_of_pa_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [1] ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      endpointBound, hinputLayout, himmediate⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, Or.inr (Or.inl himmediate)⟩

theorem exists_compactCertificateNodeFailureBoundedGraph_of_pa_large_with_inputLayout
    (paTag : Nat) (body : List Nat) (htag : 22 < paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: paTag :: body) ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_large_with_inputLayout
      paTag body htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      endpointBound, hinputLayout, himmediate⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, Or.inr (Or.inl himmediate)⟩

theorem exists_compactCertificateNodeFailureBoundedGraph_of_pa_symbol_with_inputLayout
    (paTag : Nat) (body : List Nat)
    (htag : paTag = 3 ∨ paTag = 4)
    (hfailure :
      body.length < 2 ∨
        ((paTag = 3 ∧
            ¬ ArithmeticFuncCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)) ∨
          (paTag = 4 ∧
            ¬ ArithmeticRelCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)))) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: paTag :: body) ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_inputLayout
      paTag body htag hfailure with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      endpointBound, hinputLayout, hsymbol⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, Or.inr (Or.inr (Or.inl hsymbol))⟩

theorem exists_compactCertificateNodeFailureBoundedGraph_of_pa_induction_with_inputLayout
    (formulaInput : List Nat)
    (hformula : compactFormulaTokenParser 1 formulaInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: 22 :: formulaInput) ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactCertificateNodeInductionPAFailureEndpointBoundedGraph_with_inputLayout
      formulaInput hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      endpointBound, hinputLayout, hinduction⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, Or.inr (Or.inr (Or.inr hinduction))⟩

theorem exists_compactCertificateNodeFailureBoundedGraph_of_parser_none_with_inputLayout
    (input : List Nat)
    (hparser : compactStructuralCertificateNodeParser input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hshape :=
    (compactStructuralCertificateNodeParser_eq_none_iff_failureShape
      input).mp hparser
  rcases hshape with rfl | ⟨tag, tail, rfl, hnode⟩
  · exact exists_compactCertificateNodeFailureBoundedGraph_of_outer_empty_with_inputLayout
  · rcases hnode with ⟨rfl, hpa⟩ | ⟨h0, h1, h2, h3⟩
    · rcases hpa with rfl | ⟨paTag, body, rfl, hpafailure⟩
      · exact exists_compactCertificateNodeFailureBoundedGraph_of_pa_empty_with_inputLayout
      · rcases hpafailure with hfunc | hrel | hformula | hlarge
        · rcases hfunc with ⟨rfl, hshort | hinvalid⟩
          · exact exists_compactCertificateNodeFailureBoundedGraph_of_pa_symbol_with_inputLayout
              3 body (Or.inl rfl) (Or.inl hshort)
          · exact exists_compactCertificateNodeFailureBoundedGraph_of_pa_symbol_with_inputLayout
              3 body (Or.inl rfl)
                (Or.inr (Or.inl ⟨rfl, hinvalid⟩))
        · rcases hrel with ⟨rfl, hshort | hinvalid⟩
          · exact exists_compactCertificateNodeFailureBoundedGraph_of_pa_symbol_with_inputLayout
              4 body (Or.inr rfl) (Or.inl hshort)
          · exact exists_compactCertificateNodeFailureBoundedGraph_of_pa_symbol_with_inputLayout
              4 body (Or.inr rfl)
                (Or.inr (Or.inr ⟨rfl, hinvalid⟩))
        · rcases hformula with ⟨rfl, hformula⟩
          exact exists_compactCertificateNodeFailureBoundedGraph_of_pa_induction_with_inputLayout
            body hformula
        · exact exists_compactCertificateNodeFailureBoundedGraph_of_pa_large_with_inputLayout
            paTag body hlarge
    · exact exists_compactCertificateNodeFailureBoundedGraph_of_outer_invalid_with_inputLayout
        tag tail h0 h1 h2 h3

theorem exists_compactCertificateNodeFailureBoundedGraph_of_parser_none
    (input : List Nat)
    (hparser : compactStructuralCertificateNodeParser input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactCertificateNodeFailureBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactCertificateNodeFailureBoundedGraph_of_parser_none_with_inputLayout
        input hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      endpointBound, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hgraph⟩

#print axioms compactCertificateNodeOuterFailureLiftedBoundedGraphDef_spec
#print axioms compactCertificateNodeFailureBoundedGraphDef_spec
#print axioms compactCertificateNodeFailureBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeFailureBoundedGraph.sound
#print axioms exists_compactCertificateNodeFailureBoundedGraph_of_parser_none

end FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula
