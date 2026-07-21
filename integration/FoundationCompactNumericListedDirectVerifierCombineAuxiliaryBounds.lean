import integration.FoundationCompactNumericListedDirectFormulaTransformValueBounds
import integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph

/-!
# Public weight bounds for canonical combine auxiliary tokens

The four nontrivial combine branches serialize exact formula-transform
outputs and their complete executable traces.  This file bounds those
concrete suffixes from the source values themselves.  No auxiliary suffix,
trace width, or output-size bound is accepted as an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph

private theorem compactExactFormulaTransformStateOutput_getD_weight_le
    (state : CompactFormulaTransformState) :
    compactAdditiveValueWeight
        ((compactExactFormulaTransformResult
          (compactFormulaTransformStateOutput state)).getD []) ≤
      compactAdditiveValueWeight state.2 := by
  cases hstatus : state.1.2.2 with
  | none =>
      simpa [compactFormulaTransformStateOutput,
        compactExactFormulaTransformResult, hstatus] using
          compactAdditiveValueWeight_list_pos state.2
  | some result =>
      cases result with
      | none =>
          simpa [compactFormulaTransformStateOutput,
            compactExactFormulaTransformResult, hstatus] using
              compactAdditiveValueWeight_list_pos state.2
      | some suffix =>
          cases suffix with
          | nil =>
              simp [compactFormulaTransformStateOutput,
                compactExactFormulaTransformResult, hstatus]
          | cons head tail =>
              simpa [compactFormulaTransformStateOutput,
                compactExactFormulaTransformResult, hstatus] using
                  compactAdditiveValueWeight_list_pos state.2

theorem compactExactFormulaTransformResult_getD_weight_le
    (mode binderArity : Nat) (witness tokens : List Nat)
    (hmode : mode ≤ 3) :
    compactAdditiveValueWeight
        ((compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (mode, witness) (binderArity, tokens))).getD []) ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness) := by
  let state :=
    compactFormulaTransformRun
      (mode, witness) (binderArity, tokens)
  have hget :=
    compactExactFormulaTransformStateOutput_getD_weight_le state
  have hout :=
    compactFormulaTransformCanonicalStateOutput_weight_le
      mode binderArity witness tokens hmode
  have hstate :
      compactAdditiveValueWeight state.2 ≤
        compactFormulaTransformCanonicalOutputWeightBound
          (compactAdditiveValueWeight tokens)
          (compactAdditiveValueWeight witness) := by
    simpa [state, compactFormulaTransformRun,
      compactFormulaTransformStateAt] using hout
  simpa [state, compactFormulaTransformResult] using
    hget.trans hstate

theorem compactFormulaShiftExact_getD_weight_le
    (binderArity : Nat) (tokens : List Nat) :
    compactAdditiveValueWeight
        ((compactFormulaShiftExact binderArity tokens).getD []) ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight ([] : List Nat)) := by
  simpa [compactFormulaShiftExact] using
    compactExactFormulaTransformResult_getD_weight_le
      1 binderArity [] tokens (by omega)

theorem compactFormulaSubstitutionExact_getD_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        ((compactFormulaSubstitutionExact
          binderArity (witness, tokens)).getD []) ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness) := by
  simpa [compactFormulaSubstitutionExact] using
    compactExactFormulaTransformResult_getD_weight_le
      2 binderArity witness tokens (by omega)

theorem compactFormulaNegationExact_getD_weight_le
    (binderArity : Nat) (tokens : List Nat) :
    compactAdditiveValueWeight
        ((compactFormulaNegationExact binderArity tokens).getD []) ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight ([] : List Nat)) := by
  simpa [compactFormulaNegationExact] using
    compactExactFormulaTransformResult_getD_weight_le
      3 binderArity [] tokens (by omega)

theorem compactFormulaFreeExact_getD_weight_le
    (tokens : List Nat) :
    compactAdditiveValueWeight
        ((compactFormulaFreeExact tokens).getD []) ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight ([] : List Nat)) := by
  simpa [compactFormulaFreeExact] using
    compactExactFormulaTransformResult_getD_weight_le
      0 1 [] tokens (by omega)

def compactFormulaShiftItemPublicWeightBound
    (sourceWeight : Nat) : Nat :=
  compactFormulaTransformCanonicalOutputWeightBound sourceWeight 1

def compactFormulaShiftListPublicWeightBound
    (sourceWeight : Nat) : Nat :=
  Nat.size sourceWeight + 1 +
    sourceWeight *
      compactFormulaShiftItemPublicWeightBound sourceWeight

def compactFormulaShiftTraceListPublicWeightBound
    (sourceWeight : Nat) : Nat :=
  Nat.size sourceWeight + 1 +
    sourceWeight *
      compactFormulaTransformCanonicalTraceWeightBound
        sourceWeight 1 0

theorem compactFormulaShiftItemPublicWeightBound_mono
    {left right : Nat} (h : left ≤ right) :
    compactFormulaShiftItemPublicWeightBound left ≤
      compactFormulaShiftItemPublicWeightBound right := by
  exact compactFormulaTransformCanonicalOutputWeightBound_mono
    h (Nat.le_refl 1)

theorem compactFormulaShiftListPublicWeightBound_mono
    {left right : Nat} (h : left ≤ right) :
    compactFormulaShiftListPublicWeightBound left ≤
      compactFormulaShiftListPublicWeightBound right := by
  have hsize := Nat.size_le_size h
  have hitem := compactFormulaShiftItemPublicWeightBound_mono h
  have hproduct := Nat.mul_le_mul h hitem
  unfold compactFormulaShiftListPublicWeightBound
  omega

theorem compactFormulaShiftTraceListPublicWeightBound_mono
    {left right : Nat} (h : left ≤ right) :
    compactFormulaShiftTraceListPublicWeightBound left ≤
      compactFormulaShiftTraceListPublicWeightBound right := by
  have hsize := Nat.size_le_size h
  have htrace :=
    compactFormulaTransformCanonicalTraceWeightBound_mono
      h (Nat.le_refl 1) (Nat.le_refl 0)
  have hproduct := Nat.mul_le_mul h htrace
  unfold compactFormulaShiftTraceListPublicWeightBound
  omega

theorem compactFormulaShiftCandidateList_weight_le
    (formulas : List (List Nat)) :
    compactAdditiveValueWeight
        (formulas.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []) ≤
      compactFormulaShiftListPublicWeightBound
        (compactAdditiveValueWeight formulas) := by
  let itemBound :=
    compactFormulaShiftItemPublicWeightBound
      (compactAdditiveValueWeight formulas)
  have hitems :
      ∀ shifted ∈
          formulas.map fun formula =>
            (compactFormulaShiftExact 0 formula).getD [],
        compactAdditiveValueWeight shifted ≤ itemBound := by
    intro shifted hshifted
    rcases List.mem_map.mp hshifted with
      ⟨formula, hformula, rfl⟩
    have hformulaWeight :=
      compactAdditiveValueWeight_mem_le hformula
    have hexact := compactFormulaShiftExact_getD_weight_le 0 formula
    exact hexact.trans
      (compactFormulaTransformCanonicalOutputWeightBound_mono
        hformulaWeight (by simp))
  have hraw := compactAdditiveValueWeight_list_le
    (formulas.map fun formula =>
      (compactFormulaShiftExact 0 formula).getD [])
    itemBound hitems
  have hlength :=
    compactAdditiveValueWeight_listOfLists_length_le formulas
  have hsize := Nat.size_le_size hlength
  have hproduct := Nat.mul_le_mul_right itemBound hlength
  rw [List.length_map] at hraw
  dsimp only [itemBound] at hraw hproduct ⊢
  unfold compactFormulaShiftListPublicWeightBound
  exact hraw.trans (by omega)

private theorem compactFormulaShiftExactList_eq_some_map_of_all
    (formulas : List (List Nat))
    (hall : ∀ formula ∈ formulas,
      (compactFormulaShiftExact 0 formula).isSome = true) :
    compactFormulaShiftExactList formulas =
      some (formulas.map fun formula =>
        (compactFormulaShiftExact 0 formula).getD []) := by
  induction formulas with
  | nil => simp [compactFormulaShiftExactList]
  | cons formula formulas ih =>
      have hformula := hall formula (by simp)
      have htail : ∀ tailFormula ∈ formulas,
          (compactFormulaShiftExact 0 tailFormula).isSome = true := by
        intro tailFormula htailFormula
        exact hall tailFormula (by simp [htailFormula])
      have hi := ih htail
      change compactShiftedFormulaCons formula
          (compactFormulaShiftExactList formulas) = _
      rw [hi]
      cases hshift : compactFormulaShiftExact 0 formula with
      | none => simp [hshift] at hformula
      | some shifted =>
          simp [compactShiftedFormulaCons, hshift]

private theorem compactFormulaShiftExactList_eq_none_of_failure
    (formulas : List (List Nat))
    (hfailure : ∃ formula ∈ formulas,
      (compactFormulaShiftExact 0 formula).isSome = false) :
    compactFormulaShiftExactList formulas = none := by
  induction formulas with
  | nil => simp at hfailure
  | cons formula formulas ih =>
      rcases hfailure with ⟨failedFormula, hfailedMem, hfailed⟩
      simp only [List.mem_cons] at hfailedMem
      rcases hfailedMem with hhead | htail
      · subst failedFormula
        change compactShiftedFormulaCons formula
          (compactFormulaShiftExactList formulas) = none
        cases hshift : compactFormulaShiftExact 0 formula with
        | none => simp [compactShiftedFormulaCons, hshift]
        | some shifted => simp [hshift] at hfailed
      · have hi := ih ⟨failedFormula, htail, hfailed⟩
        change compactShiftedFormulaCons formula
          (compactFormulaShiftExactList formulas) = none
        rw [hi]
        cases hshift : compactFormulaShiftExact 0 formula <;>
          simp [compactShiftedFormulaCons, hshift]

theorem compactFormulaShiftExactList_getD_weight_le
    (formulas : List (List Nat)) :
    compactAdditiveValueWeight
        ((compactFormulaShiftExactList formulas).getD []) ≤
      compactFormulaShiftListPublicWeightBound
        (compactAdditiveValueWeight formulas) := by
  by_cases hall : ∀ formula ∈ formulas,
      (compactFormulaShiftExact 0 formula).isSome = true
  · rw [compactFormulaShiftExactList_eq_some_map_of_all formulas hall]
    simpa using compactFormulaShiftCandidateList_weight_le formulas
  · push Not at hall
    have hfailure : ∃ formula ∈ formulas,
        (compactFormulaShiftExact 0 formula).isSome = false := by
      rcases hall with ⟨formula, hformula, hnotTrue⟩
      refine ⟨formula, hformula, ?_⟩
      cases hvalue :
          (compactFormulaShiftExact 0 formula).isSome <;>
        simp_all
    rw [compactFormulaShiftExactList_eq_none_of_failure
      formulas hfailure]
    have hpositive :
        1 ≤ compactFormulaShiftListPublicWeightBound
          (compactAdditiveValueWeight formulas) := by
      unfold compactFormulaShiftListPublicWeightBound
      omega
    simpa using hpositive

theorem compactFormulaShiftTraceList_weight_le
    (formulas : List (List Nat)) :
    compactAdditiveValueWeight
        (compactFormulaShiftTraceList formulas) ≤
      compactFormulaShiftTraceListPublicWeightBound
        (compactAdditiveValueWeight formulas) := by
  let traceBound :=
    compactFormulaTransformCanonicalTraceWeightBound
      (compactAdditiveValueWeight formulas) 1 0
  have hitems :
      ∀ trace ∈ compactFormulaShiftTraceList formulas,
        compactAdditiveValueWeight trace ≤ traceBound := by
    intro trace htrace
    rw [compactFormulaShiftTraceList] at htrace
    rcases List.mem_map.mp htrace with
      ⟨formula, hformula, rfl⟩
    have hformulaWeight :=
      compactAdditiveValueWeight_mem_le hformula
    have hcanonical :=
      compactFormulaTransformCanonicalStateTrace_weight_le
        1 0 [] formula (by omega)
    exact hcanonical.trans
      (compactFormulaTransformCanonicalTraceWeightBound_mono
        hformulaWeight (by simp) (Nat.le_refl 0))
  have hraw := compactAdditiveValueWeight_list_le
    (compactFormulaShiftTraceList formulas)
    traceBound hitems
  have hlength :=
    compactAdditiveValueWeight_listOfLists_length_le formulas
  have htraceLength :
      (compactFormulaShiftTraceList formulas).length =
        formulas.length := by
    simp [compactFormulaShiftTraceList]
  have hsize := Nat.size_le_size hlength
  have hproduct := Nat.mul_le_mul_right traceBound hlength
  rw [htraceLength] at hraw
  dsimp only [traceBound] at hraw hproduct ⊢
  unfold compactFormulaShiftTraceListPublicWeightBound
  exact hraw.trans (by omega)

def compactNumericExsCombineAuxiliaryTokenWeightBound
    (formulaWeight witnessWeight : Nat) : Nat :=
  compactFormulaTransformCanonicalOutputWeightBound
      formulaWeight witnessWeight +
    1 +
    compactFormulaTransformCanonicalTraceWeightBound
      formulaWeight witnessWeight 1

def compactNumericCutCombineAuxiliaryTokenWeightBound
    (formulaWeight : Nat) : Nat :=
  compactFormulaTransformCanonicalOutputWeightBound
      formulaWeight 1 +
    1 +
    compactFormulaTransformCanonicalTraceWeightBound
      formulaWeight 1 0

def compactNumericShiftCombineAuxiliaryTokenWeightBound
    (premiseWeight : Nat) : Nat :=
  1 +
    2 * compactFormulaShiftListPublicWeightBound premiseWeight +
    compactFormulaShiftTraceListPublicWeightBound premiseWeight

def compactNumericAllCombineAuxiliaryTokenWeightBound
    (gammaWeight formulaWeight : Nat) : Nat :=
  compactFormulaTransformCanonicalOutputWeightBound
      formulaWeight 1 +
    1 +
    compactFormulaTransformCanonicalTraceWeightBound
      formulaWeight 1 1 +
    2 * compactFormulaShiftListPublicWeightBound gammaWeight +
    compactFormulaShiftTraceListPublicWeightBound gammaWeight

theorem compactNumericExsCombineAuxiliaryTokens_weight_le
    (formula witness : List Nat) :
    compactAdditiveTokenWeight
        (compactNumericExsCombineAuxiliaryTokens formula witness) ≤
      compactNumericExsCombineAuxiliaryTokenWeightBound
        (compactAdditiveValueWeight formula)
        (compactAdditiveValueWeight witness) := by
  have htransformed :=
    compactFormulaSubstitutionExact_getD_weight_le
      1 witness formula
  have htrace :=
    compactFormulaTransformCanonicalStateTrace_weight_le
      2 1 witness formula (by omega)
  simp only [compactNumericExsCombineAuxiliaryTokens,
    compactAdditiveTokenWeight_append]
  change
    compactAdditiveValueWeight
        ((compactFormulaSubstitutionExact
          1 (witness, formula)).getD []) +
      compactAdditiveValueWeight ([] : List Nat) +
      compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (2, witness)
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 1 formula)) ≤ _
  unfold compactNumericExsCombineAuxiliaryTokenWeightBound
  simp only [compactAdditiveValueWeight_list,
    List.length_nil, List.map_nil, List.sum_nil, Nat.size_zero,
    Nat.zero_add, Nat.add_zero] at htransformed htrace ⊢
  omega

theorem compactNumericCutCombineAuxiliaryTokens_weight_le
    (formula : List Nat) :
    compactAdditiveTokenWeight
        (compactNumericCutCombineAuxiliaryTokens formula) ≤
      compactNumericCutCombineAuxiliaryTokenWeightBound
        (compactAdditiveValueWeight formula) := by
  have htransformed :=
    compactFormulaNegationExact_getD_weight_le 0 formula
  have htrace :=
    compactFormulaTransformCanonicalStateTrace_weight_le
      3 0 [] formula (by omega)
  simp only [compactNumericCutCombineAuxiliaryTokens,
    compactAdditiveTokenWeight_append]
  change
    compactAdditiveValueWeight
        ((compactFormulaNegationExact 0 formula).getD []) +
      compactAdditiveValueWeight ([] : List Nat) +
      compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (3, [])
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 0 formula)) ≤ _
  unfold compactNumericCutCombineAuxiliaryTokenWeightBound
  simp only [compactAdditiveValueWeight_list,
    List.length_nil, List.map_nil, List.sum_nil, Nat.size_zero,
    Nat.zero_add, Nat.add_zero] at htransformed htrace ⊢
  omega

theorem compactNumericShiftCombineAuxiliaryTokens_weight_le
    (premise : List (List Nat)) :
    compactAdditiveTokenWeight
        (compactNumericShiftCombineAuxiliaryTokens premise) ≤
      compactNumericShiftCombineAuxiliaryTokenWeightBound
        (compactAdditiveValueWeight premise) := by
  have hcandidates :=
    compactFormulaShiftCandidateList_weight_le premise
  have hshifted :=
    compactFormulaShiftExactList_getD_weight_le premise
  have htraces :=
    compactFormulaShiftTraceList_weight_le premise
  simp only [compactNumericShiftCombineAuxiliaryTokens,
    compactAdditiveTokenWeight_append]
  change
    compactAdditiveValueWeight ([] : List Nat) +
      compactAdditiveValueWeight
        (premise.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []) +
      compactAdditiveValueWeight
        ((compactFormulaShiftExactList premise).getD []) +
      compactAdditiveValueWeight
        (compactFormulaShiftTraceList premise) ≤ _
  unfold compactNumericShiftCombineAuxiliaryTokenWeightBound
  simp only [compactAdditiveValueWeight_list,
    List.length_nil, List.map_nil, List.sum_nil, Nat.size_zero,
    Nat.zero_add, Nat.add_zero] at hcandidates hshifted htraces ⊢
  omega

theorem compactNumericAllCombineAuxiliaryTokens_weight_le
    (Gamma : List (List Nat)) (formula : List Nat) :
    compactAdditiveTokenWeight
        (compactNumericAllCombineAuxiliaryTokens Gamma formula) ≤
      compactNumericAllCombineAuxiliaryTokenWeightBound
        (compactAdditiveValueWeight Gamma)
        (compactAdditiveValueWeight formula) := by
  have hfreed := compactFormulaFreeExact_getD_weight_le formula
  have hfreeTrace :=
    compactFormulaTransformCanonicalStateTrace_weight_le
      0 1 [] formula (by omega)
  have hcandidates :=
    compactFormulaShiftCandidateList_weight_le Gamma
  have hshifted :=
    compactFormulaShiftExactList_getD_weight_le Gamma
  have hshiftTraces :=
    compactFormulaShiftTraceList_weight_le Gamma
  simp only [compactNumericAllCombineAuxiliaryTokens,
    compactAdditiveTokenWeight_append]
  change
    compactAdditiveValueWeight
        ((compactFormulaFreeExact formula).getD []) +
      compactAdditiveValueWeight ([] : List Nat) +
      compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (0, [])
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 1 formula)) +
      compactAdditiveValueWeight
        (Gamma.map fun candidateFormula =>
          (compactFormulaShiftExact 0 candidateFormula).getD []) +
      compactAdditiveValueWeight
        ((compactFormulaShiftExactList Gamma).getD []) +
      compactAdditiveValueWeight
        (compactFormulaShiftTraceList Gamma) ≤ _
  unfold compactNumericAllCombineAuxiliaryTokenWeightBound
  simp only [compactAdditiveValueWeight_list,
    List.length_nil, List.map_nil, List.sum_nil, Nat.size_zero,
    Nat.zero_add, Nat.add_zero] at hfreed hfreeTrace hcandidates hshifted hshiftTraces ⊢
  omega

def compactNumericVerifierCombineAuxiliaryTokenWeightBound
    (stateWeight : Nat) : Nat :=
  compactFormulaTransformCanonicalOutputWeightBound
      stateWeight stateWeight +
    1 +
    compactFormulaTransformCanonicalTraceWeightBound
      stateWeight stateWeight 1 +
    2 * compactFormulaShiftListPublicWeightBound stateWeight +
    compactFormulaShiftTraceListPublicWeightBound stateWeight

theorem compactNumericVerifierCombineAuxiliaryTokenWeightBound_mono
    {left right : Nat} (h : left ≤ right) :
    compactNumericVerifierCombineAuxiliaryTokenWeightBound left ≤
      compactNumericVerifierCombineAuxiliaryTokenWeightBound right := by
  have houtput :=
    compactFormulaTransformCanonicalOutputWeightBound_mono h h
  have htrace :=
    compactFormulaTransformCanonicalTraceWeightBound_mono
      h h (Nat.le_refl 1)
  have hlist := compactFormulaShiftListPublicWeightBound_mono h
  have htraces := compactFormulaShiftTraceListPublicWeightBound_mono h
  unfold compactNumericVerifierCombineAuxiliaryTokenWeightBound
  omega

theorem compactNumericExsCombineAuxiliaryTokens_weight_le_public
    {formula witness : List Nat} {stateWeight : Nat}
    (hformula : compactAdditiveValueWeight formula ≤ stateWeight)
    (hwitness : compactAdditiveValueWeight witness ≤ stateWeight) :
    compactAdditiveTokenWeight
        (compactNumericExsCombineAuxiliaryTokens formula witness) ≤
      compactNumericVerifierCombineAuxiliaryTokenWeightBound stateWeight := by
  have hraw :=
    compactNumericExsCombineAuxiliaryTokens_weight_le formula witness
  have houtput :=
    compactFormulaTransformCanonicalOutputWeightBound_mono
      hformula hwitness
  have htrace :=
    compactFormulaTransformCanonicalTraceWeightBound_mono
      hformula hwitness (Nat.le_refl 1)
  unfold compactNumericExsCombineAuxiliaryTokenWeightBound at hraw
  unfold compactNumericVerifierCombineAuxiliaryTokenWeightBound
  omega

theorem compactNumericCutCombineAuxiliaryTokens_weight_le_public
    {formula : List Nat} {stateWeight : Nat}
    (hformula : compactAdditiveValueWeight formula ≤ stateWeight)
    (hpositive : 1 ≤ stateWeight) :
    compactAdditiveTokenWeight
        (compactNumericCutCombineAuxiliaryTokens formula) ≤
      compactNumericVerifierCombineAuxiliaryTokenWeightBound stateWeight := by
  have hraw :=
    compactNumericCutCombineAuxiliaryTokens_weight_le formula
  have houtput :=
    compactFormulaTransformCanonicalOutputWeightBound_mono
      hformula hpositive
  have htrace :
      compactFormulaTransformCanonicalTraceWeightBound
          (compactAdditiveValueWeight formula) 1 0 ≤
        compactFormulaTransformCanonicalTraceWeightBound
          stateWeight stateWeight 1 :=
    compactFormulaTransformCanonicalTraceWeightBound_mono
      hformula hpositive (by omega)
  unfold compactNumericCutCombineAuxiliaryTokenWeightBound at hraw
  unfold compactNumericVerifierCombineAuxiliaryTokenWeightBound
  omega

theorem compactNumericShiftCombineAuxiliaryTokens_weight_le_public
    {premise : List (List Nat)} {stateWeight : Nat}
    (hpremise : compactAdditiveValueWeight premise ≤ stateWeight) :
    compactAdditiveTokenWeight
        (compactNumericShiftCombineAuxiliaryTokens premise) ≤
      compactNumericVerifierCombineAuxiliaryTokenWeightBound stateWeight := by
  have hraw :=
    compactNumericShiftCombineAuxiliaryTokens_weight_le premise
  have hlist :=
    compactFormulaShiftListPublicWeightBound_mono hpremise
  have htraces :=
    compactFormulaShiftTraceListPublicWeightBound_mono hpremise
  unfold compactNumericShiftCombineAuxiliaryTokenWeightBound at hraw
  unfold compactNumericVerifierCombineAuxiliaryTokenWeightBound
  omega

theorem compactNumericAllCombineAuxiliaryTokens_weight_le_public
    {Gamma : List (List Nat)} {formula : List Nat} {stateWeight : Nat}
    (hGamma : compactAdditiveValueWeight Gamma ≤ stateWeight)
    (hformula : compactAdditiveValueWeight formula ≤ stateWeight)
    (hpositive : 1 ≤ stateWeight) :
    compactAdditiveTokenWeight
        (compactNumericAllCombineAuxiliaryTokens Gamma formula) ≤
      compactNumericVerifierCombineAuxiliaryTokenWeightBound stateWeight := by
  have hraw :=
    compactNumericAllCombineAuxiliaryTokens_weight_le Gamma formula
  have houtput :=
    compactFormulaTransformCanonicalOutputWeightBound_mono
      hformula hpositive
  have htrace :=
    compactFormulaTransformCanonicalTraceWeightBound_mono
      hformula hpositive (Nat.le_refl 1)
  have hlist :=
    compactFormulaShiftListPublicWeightBound_mono hGamma
  have htraces :=
    compactFormulaShiftTraceListPublicWeightBound_mono hGamma
  unfold compactNumericAllCombineAuxiliaryTokenWeightBound at hraw
  unfold compactNumericVerifierCombineAuxiliaryTokenWeightBound
  omega

#print axioms compactExactFormulaTransformResult_getD_weight_le
#print axioms compactFormulaShiftExact_getD_weight_le
#print axioms compactFormulaSubstitutionExact_getD_weight_le
#print axioms compactFormulaNegationExact_getD_weight_le
#print axioms compactFormulaFreeExact_getD_weight_le
#print axioms compactFormulaShiftCandidateList_weight_le
#print axioms compactFormulaShiftExactList_getD_weight_le
#print axioms compactFormulaShiftTraceList_weight_le
#print axioms compactNumericExsCombineAuxiliaryTokens_weight_le_public
#print axioms compactNumericCutCombineAuxiliaryTokens_weight_le_public
#print axioms compactNumericShiftCombineAuxiliaryTokens_weight_le_public
#print axioms compactNumericAllCombineAuxiliaryTokens_weight_le_public

end FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds
