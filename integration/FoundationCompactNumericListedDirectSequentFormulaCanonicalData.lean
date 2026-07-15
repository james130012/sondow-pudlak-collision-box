import integration.FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts

/-!
# Canonical direct data for a successful sequent formula parse

For a real formula list and a final suffix, this file constructs every
intermediate suffix and one genuine direct parser trace for each formula.
The first and final suffixes are pinned to the public parser coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaCanonicalData

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace

/-- A canonical formula list has a complete sequence of real parser traces,
including exact first/final endpoints and the token concatenation at every
step. -/
theorem exists_compactSequentFormulaCanonicalDirectData
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) :
    ∃ suffixes : List (List Nat),
    ∃ parserTraces : List CompactFormulaTokenParserDirectTrace,
      suffixes.length = Gamma.length + 1 ∧
      parserTraces.length = Gamma.length ∧
      suffixes.getI 0 =
        Gamma.flatMap compactArithmeticFormulaTokens ++ suffix ∧
      suffixes.getI Gamma.length = suffix ∧
      ∀ index < Gamma.length,
        CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          (Gamma.map compactArithmeticFormulaTokens).getI index ++
            suffixes.getI (index + 1) := by
  induction Gamma with
  | nil =>
      refine ⟨[suffix], [], by simp, by simp, by simp, by simp, ?_⟩
      intro index hindex
      simp at hindex
  | cons formula Gamma ih =>
      rcases ih with
        ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
          hfirst, hfinal, hsteps⟩
      let rest := Gamma.flatMap compactArithmeticFormulaTokens ++ suffix
      have hparse : compactFormulaTokenParser 0
          (compactArithmeticFormulaTokens formula ++ rest) = some rest :=
        compactFormulaTokenParser_canonical_append formula rest
      rcases
          (compactFormulaTokenParser_eq_some_iff_exists_directTrace
            0 (compactArithmeticFormulaTokens formula ++ rest) rest).mp
            hparse with
        ⟨headTrace, hheadTrace⟩
      let current := compactArithmeticFormulaTokens formula ++ rest
      refine ⟨current :: suffixes, headTrace :: parserTraces,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [hsuffixCount]
      · simp [hparserCount]
      · simp [current, rest]
      · simpa [List.getI_cons_succ] using hfinal
      · intro index hindex
        cases index with
        | zero =>
            have hnext : suffixes.getI 0 = rest := by
              simpa [rest] using hfirst
            constructor
            · simpa [current, hnext] using hheadTrace
            · simp [current, hnext]
        | succ index =>
            have hindexTail : index < Gamma.length := by
              simpa using hindex
            have hstep := hsteps index hindexTail
            simpa [List.getI_cons_succ] using hstep

#print axioms exists_compactSequentFormulaCanonicalDirectData

end FoundationCompactNumericListedDirectSequentFormulaCanonicalData
