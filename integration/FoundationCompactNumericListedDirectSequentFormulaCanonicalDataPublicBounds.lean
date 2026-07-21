import integration.FoundationCompactNumericListedDirectSequentFormulaCanonicalData
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public weight bounds for canonical sequent parser data

The canonical successful sequent construction introduces every intermediate
token suffix and one complete formula-parser trace per formula.  This module
shows that both aggregate lists have explicit polynomial weight bounds in the
weight of the original count-prefixed sequent token stream.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData

def compactSequentFormulaCanonicalSuffixesWeightBound
    (streamWeight : Nat) : Nat :=
  Nat.size (streamWeight + 1) + 1 +
    (streamWeight + 1) * streamWeight

def compactSequentFormulaCanonicalParserTracesWeightBound
    (streamWeight : Nat) : Nat :=
  Nat.size streamWeight + 1 +
    streamWeight *
      compactNumericRootSyntaxParserTraceWeightBound streamWeight

theorem exists_compactSequentFormulaCanonicalDirectData_with_publicBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) :
    let input := compactSequentListTokens Gamma ++ suffix
    let streamWeight := compactAdditiveValueWeight input
    ∃ suffixes : List (List Nat),
    ∃ parserTraces : List CompactFormulaTokenParserDirectTrace,
      suffixes.length = Gamma.length + 1 ∧
      parserTraces.length = Gamma.length ∧
      suffixes.getI 0 =
        Gamma.flatMap compactArithmeticFormulaTokens ++ suffix ∧
      suffixes.getI Gamma.length = suffix ∧
      (∀ index < Gamma.length,
        CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          (Gamma.map compactArithmeticFormulaTokens).getI index ++
            suffixes.getI (index + 1)) ∧
      compactAdditiveValueWeight suffixes <=
        compactSequentFormulaCanonicalSuffixesWeightBound streamWeight ∧
      compactAdditiveValueWeight parserTraces <=
        compactSequentFormulaCanonicalParserTracesWeightBound
          streamWeight := by
  let input := compactSequentListTokens Gamma ++ suffix
  let streamWeight := compactAdditiveValueWeight input
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma suffix with
    ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
      hfirst, hfinal, hsteps⟩
  have hinputLength : input.length <= streamWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hGammaLength : Gamma.length <= streamWeight := by
    have hformulaLength :=
      formulaList_length_le_flatMap_tokenLength Gamma
    have hlength :
        Gamma.length <=
          (compactSequentListTokens Gamma ++ suffix).length := by
      simp only [compactSequentListTokens, List.length_append,
        List.length_cons]
      omega
    exact hlength.trans (by simpa only [input] using hinputLength)
  have hfirstSuffix :
      Gamma.flatMap compactArithmeticFormulaTokens ++ suffix <:+ input := by
    refine ⟨[Gamma.length], ?_⟩
    simp [input, compactSequentListTokens]
  have hsuffixAt :
      ∀ index, index <= Gamma.length →
        compactAdditiveValueWeight (suffixes.getI index) <= streamWeight := by
    intro index hindex
    induction index with
    | zero =>
        rw [hfirst]
        exact compactAdditiveValueWeight_suffix_le hfirstSuffix
    | succ index ih =>
        have hlt : index < Gamma.length := by omega
        have hstep := hsteps index hlt
        have hsuffix :
            suffixes.getI (index + 1) <:+ suffixes.getI index :=
          ⟨(Gamma.map compactArithmeticFormulaTokens).getI index,
            hstep.2.symm⟩
        exact (compactAdditiveValueWeight_suffix_le hsuffix).trans
          (ih (Nat.le_of_lt hlt))
  have hsuffixMember :
      ∀ value ∈ suffixes,
        compactAdditiveValueWeight value <= streamWeight := by
    intro value hvalue
    obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hvalue
    have hle : index <= Gamma.length := by
      rw [hsuffixCount] at hindex
      omega
    have hbound := hsuffixAt index hle
    rw [List.getI_eq_getElem suffixes hindex, hget] at hbound
    exact hbound
  have hsuffixLength : suffixes.length <= streamWeight + 1 := by
    rw [hsuffixCount]
    omega
  have hsuffixRaw :=
    compactAdditiveValueWeight_list_le suffixes streamWeight hsuffixMember
  have hsuffixSize := Nat.size_le_size hsuffixLength
  have hsuffixProduct :=
    Nat.mul_le_mul_right streamWeight hsuffixLength
  have hsuffixWeight :
      compactAdditiveValueWeight suffixes <=
        compactSequentFormulaCanonicalSuffixesWeightBound streamWeight := by
    unfold compactSequentFormulaCanonicalSuffixesWeightBound
    omega
  have hparserMember :
      ∀ parserTrace ∈ parserTraces,
        compactAdditiveValueWeight parserTrace <=
          compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
    intro parserTrace hparserTrace
    obtain ⟨index, hindex, hget⟩ :=
      List.mem_iff_getElem.mp hparserTrace
    have hindexGamma : index < Gamma.length := by
      rw [hparserCount] at hindex
      exact hindex
    have hstep := hsteps index hindexGamma
    have hstream := hsuffixAt index (Nat.le_of_lt hindexGamma)
    have htrace :=
      compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
        hstep.1 hstream (by omega)
    rw [List.getI_eq_getElem parserTraces hindex, hget] at htrace
    exact htrace
  have hparserRaw :=
    compactAdditiveValueWeight_list_le parserTraces
      (compactNumericRootSyntaxParserTraceWeightBound streamWeight)
      hparserMember
  have hparserLength : parserTraces.length <= streamWeight := by
    rw [hparserCount]
    exact hGammaLength
  have hparserSize := Nat.size_le_size hparserLength
  have hparserProduct :=
    Nat.mul_le_mul_right
      (compactNumericRootSyntaxParserTraceWeightBound streamWeight)
      hparserLength
  have hparserWeight :
      compactAdditiveValueWeight parserTraces <=
        compactSequentFormulaCanonicalParserTracesWeightBound
          streamWeight := by
    unfold compactSequentFormulaCanonicalParserTracesWeightBound
    omega
  exact ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
    hfirst, hfinal, hsteps, hsuffixWeight, hparserWeight⟩

#print axioms
  exists_compactSequentFormulaCanonicalDirectData_with_publicBounds

end FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
