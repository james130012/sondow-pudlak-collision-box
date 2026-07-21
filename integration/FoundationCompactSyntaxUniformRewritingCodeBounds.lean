import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-!
# Polynomial code bounds for a uniform rewriting

Lifting a rewriting through one binder preserves the symbol count of every
old variable image.  Its binary code grows only by twice that symbol count.
Tracking both coordinates gives a polynomial formula-code bound without the
exponential loss of repeatedly tripling a single coarse coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactSyntaxUniformRewritingCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCanonicalDecodeLength
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

def UniformRewritingImageBound
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (codeBound symbolBound : Nat) : Prop :=
  (forall index,
    (binaryTermCode
      (rewriting (#index : ArithmeticSemiterm Nat sourceArity))).length <=
        codeBound) ∧
  (forall index,
    termSymbolCount
      (rewriting (#index : ArithmeticSemiterm Nat sourceArity)) <=
        symbolBound) ∧
  (forall index,
    rewriting (&index : ArithmeticSemiterm Nat sourceArity) =
      (&index : ArithmeticSemiterm Nat targetArity))

theorem UniformRewritingImageBound.ofCodeBound
    {sourceArity targetArity : Nat}
    {rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity}
    {imageBound : Nat}
    (hbound : RewritingImageCodeBound rewriting imageBound) :
    UniformRewritingImageBound rewriting (imageBound + 4)
      (imageBound + 1) := by
  constructor
  · intro index
    exact (hbound.1 index).trans (by omega)
  constructor
  · intro index
    exact (termSymbolCount_le_binaryTermCode_length
      (rewriting (#index : ArithmeticSemiterm Nat sourceArity))).trans
        ((hbound.1 index).trans (by omega))
  · exact hbound.2

theorem UniformRewritingImageBound.q
    {sourceArity targetArity codeBound symbolBound : Nat}
    {rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity}
    (hcode : 4 <= codeBound)
    (hsymbol : 1 <= symbolBound)
    (hbound : UniformRewritingImageBound rewriting codeBound symbolBound) :
    UniformRewritingImageBound rewriting.q
      (codeBound + 2 * symbolBound) symbolBound := by
  constructor
  · intro index
    cases index using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, binaryTermCode,
          binaryNatCode_length]
        omega
    | succ index =>
        rw [Rew.q_bvar_succ]
        exact (binaryTermCode_bShift_length_le_add_symbols
          (rewriting (#index : ArithmeticSemiterm Nat sourceArity))).trans
            (Nat.add_le_add (hbound.1 index)
              (Nat.mul_le_mul_left 2 (hbound.2.1 index)))
  constructor
  · intro index
    cases index using Fin.cases with
    | zero =>
        simpa [termSymbolCount] using hsymbol
    | succ index =>
        rw [Rew.q_bvar_succ, termSymbolCount_bShift]
        exact hbound.2.1 index
  · intro index
    rw [Rew.q_fvar, hbound.2.2 index]
    simp

theorem binaryTermCode_rewriting_length_le_uniform
    {sourceArity targetArity codeBound symbolBound : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (hcode : 1 <= codeBound)
    (hbound : UniformRewritingImageBound rewriting codeBound symbolBound) :
    forall term : ArithmeticSemiterm Nat sourceArity,
      (binaryTermCode (rewriting term)).length <=
        codeBound * (binaryTermCode term).length
  | #index => by
      have hinput := four_le_binaryTermCode_length
        (#index : ArithmeticSemiterm Nat sourceArity)
      have hwiden : codeBound <=
          codeBound * (binaryTermCode
            (#index : ArithmeticSemiterm Nat sourceArity)).length := by
        have hmul := payload_le_factor_mul_payload
          (factor := (binaryTermCode
            (#index : ArithmeticSemiterm Nat sourceArity)).length)
          (payload := codeBound) (by omega)
        simpa [Nat.mul_comm] using hmul
      exact (hbound.1 index).trans hwiden
  | &index => by
      rw [hbound.2.2 index]
      exact payload_le_factor_mul_payload hcode
  | .func functionSymbol arguments => by
      let header :=
        (binaryNatCode 2).length +
          (binaryNatCode (List.ofFn arguments).length).length +
          (binaryNatCode (Encodable.encode functionSymbol)).length
      have hchildren :
          Finset.univ.sum (fun index =>
              (binaryTermCode (rewriting (arguments index))).length) <=
            Finset.univ.sum (fun index =>
              codeBound * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ =>
          binaryTermCode_rewriting_length_le_uniform rewriting hcode hbound
            (arguments index))
      have hchildren' :
          Finset.univ.sum (fun index =>
              (binaryTermCode ((rewriting ∘ arguments) index)).length) <=
            codeBound * Finset.univ.sum (fun index =>
              (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum (fun index =>
                codeBound * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      simp only [Rew.func, binaryTermCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      simpa [header] using
        (header_payload_le_factor_mul
          (factor := codeBound) (header := header) hcode hchildren')

def uniformRewritingFormulaFactor
    (codeBound symbolBound formulaSymbols : Nat) : Nat :=
  codeBound + 2 * formulaSymbols * symbolBound

theorem four_le_uniformRewritingFormulaFactor
    {codeBound symbolBound formulaSymbols : Nat}
    (hcode : 4 <= codeBound) :
    4 <= uniformRewritingFormulaFactor codeBound symbolBound
      formulaSymbols := by
  unfold uniformRewritingFormulaFactor
  omega

theorem binaryFormulaCode_rewriting_length_le_factor
    {sourceArity : Nat}
    (formula : ArithmeticSemiformula Nat sourceArity) :
    forall {targetArity codeBound symbolBound : Nat}
      (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity),
      4 <= codeBound ->
      1 <= symbolBound ->
      UniformRewritingImageBound rewriting codeBound symbolBound ->
      (binaryFormulaCode (rewriting ▹ formula)).length <=
        uniformRewritingFormulaFactor codeBound symbolBound
            (formulaSymbolCount formula) *
          (binaryFormulaCode formula).length := by
  induction formula using Semiformula.rec' with
  | hverum =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      exact payload_le_factor_mul_payload
        ((four_le_uniformRewritingFormulaFactor
          (formulaSymbols := formulaSymbolCount ⊤) hcode).trans' (by omega))
  | hfalsum =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      exact payload_le_factor_mul_payload
        ((four_le_uniformRewritingFormulaFactor
          (formulaSymbols := formulaSymbolCount ⊥) hcode).trans' (by omega))
  | hrel relationSymbol arguments =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      let factor := uniformRewritingFormulaFactor codeBound symbolBound
        (formulaSymbolCount (Semiformula.rel relationSymbol arguments))
      let header :=
        (binaryNatCode 0).length +
          (binaryNatCode (List.ofFn arguments).length).length +
          (binaryNatCode (Encodable.encode relationSymbol)).length
      have hcodeFactor : codeBound <= factor := by
        dsimp only [factor]
        unfold uniformRewritingFormulaFactor
        omega
      have hchildren :
          Finset.univ.sum (fun index =>
              (binaryTermCode (rewriting (arguments index))).length) <=
            Finset.univ.sum (fun index =>
              factor * (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (binaryTermCode_rewriting_length_le_uniform rewriting
          (hcode.trans' (by omega)) hbound (arguments index)).trans
            (Nat.mul_le_mul_right _ hcodeFactor)
      have hchildren' :
          Finset.univ.sum (fun index =>
              (binaryTermCode ((rewriting ∘ arguments) index)).length) <=
            factor * Finset.univ.sum (fun index =>
              (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      simp only [Semiformula.rew_rel, binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      simpa [factor, header] using
        (header_payload_le_factor_mul
          (factor := factor) (header := header)
          ((four_le_uniformRewritingFormulaFactor
            (formulaSymbols := formulaSymbolCount
              (Semiformula.rel relationSymbol arguments)) hcode).trans'
                (by omega)) hchildren')
  | hnrel relationSymbol arguments =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      let factor := uniformRewritingFormulaFactor codeBound symbolBound
        (formulaSymbolCount (Semiformula.nrel relationSymbol arguments))
      let header :=
        (binaryNatCode 1).length +
          (binaryNatCode (List.ofFn arguments).length).length +
          (binaryNatCode (Encodable.encode relationSymbol)).length
      have hcodeFactor : codeBound <= factor := by
        dsimp only [factor]
        unfold uniformRewritingFormulaFactor
        omega
      have hchildren :
          Finset.univ.sum (fun index =>
              (binaryTermCode (rewriting (arguments index))).length) <=
            Finset.univ.sum (fun index =>
              factor * (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (binaryTermCode_rewriting_length_le_uniform rewriting
          (hcode.trans' (by omega)) hbound (arguments index)).trans
            (Nat.mul_le_mul_right _ hcodeFactor)
      have hchildren' :
          Finset.univ.sum (fun index =>
              (binaryTermCode ((rewriting ∘ arguments) index)).length) <=
            factor * Finset.univ.sum (fun index =>
              (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      simp only [Semiformula.rew_nrel, binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      simpa [factor, header] using
        (header_payload_le_factor_mul
          (factor := factor) (header := header)
          ((four_le_uniformRewritingFormulaFactor
            (formulaSymbols := formulaSymbolCount
              (Semiformula.nrel relationSymbol arguments)) hcode).trans'
                (by omega)) hchildren')
  | hand left right ihLeft ihRight =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      let factor := uniformRewritingFormulaFactor codeBound symbolBound
        (formulaSymbolCount (left ⋏ right))
      have hleft := ihLeft rewriting hcode hsymbol hbound
      have hright := ihRight rewriting hcode hsymbol hbound
      have hleftFactor :
          uniformRewritingFormulaFactor codeBound symbolBound
              (formulaSymbolCount left) <= factor := by
        dsimp only [factor]
        simp only [formulaSymbolCount]
        unfold uniformRewritingFormulaFactor
        gcongr
        omega
      have hrightFactor :
          uniformRewritingFormulaFactor codeBound symbolBound
              (formulaSymbolCount right) <= factor := by
        dsimp only [factor]
        simp only [formulaSymbolCount]
        unfold uniformRewritingFormulaFactor
        gcongr
        omega
      have hleft' := hleft.trans (Nat.mul_le_mul_right _ hleftFactor)
      have hright' := hright.trans (Nat.mul_le_mul_right _ hrightFactor)
      simpa [factor, binaryFormulaCode, Nat.add_assoc] using
        (header_two_payloads_le_factor_mul
          (factor := factor) (header := (binaryNatCode 4).length)
          ((four_le_uniformRewritingFormulaFactor
            (formulaSymbols := formulaSymbolCount (left ⋏ right))
            hcode).trans' (by omega)) hleft' hright')
  | hor left right ihLeft ihRight =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      let factor := uniformRewritingFormulaFactor codeBound symbolBound
        (formulaSymbolCount (left ⋎ right))
      have hleft := ihLeft rewriting hcode hsymbol hbound
      have hright := ihRight rewriting hcode hsymbol hbound
      have hleftFactor :
          uniformRewritingFormulaFactor codeBound symbolBound
              (formulaSymbolCount left) <= factor := by
        dsimp only [factor]
        simp only [formulaSymbolCount]
        unfold uniformRewritingFormulaFactor
        gcongr
        omega
      have hrightFactor :
          uniformRewritingFormulaFactor codeBound symbolBound
              (formulaSymbolCount right) <= factor := by
        dsimp only [factor]
        simp only [formulaSymbolCount]
        unfold uniformRewritingFormulaFactor
        gcongr
        omega
      have hleft' := hleft.trans (Nat.mul_le_mul_right _ hleftFactor)
      have hright' := hright.trans (Nat.mul_le_mul_right _ hrightFactor)
      simpa [factor, binaryFormulaCode, Nat.add_assoc] using
        (header_two_payloads_le_factor_mul
          (factor := factor) (header := (binaryNatCode 5).length)
          ((four_le_uniformRewritingFormulaFactor
            (formulaSymbols := formulaSymbolCount (left ⋎ right))
            hcode).trans' (by omega)) hleft' hright')
  | hall body ih =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      have hq := hbound.q hcode hsymbol
      have hbody := ih rewriting.q (by omega) hsymbol hq
      have hfactor :
          uniformRewritingFormulaFactor
              (codeBound + 2 * symbolBound) symbolBound
              (formulaSymbolCount body) =
            uniformRewritingFormulaFactor codeBound symbolBound
              (formulaSymbolCount (∀⁰ body)) := by
        simp [uniformRewritingFormulaFactor, formulaSymbolCount,
          Nat.add_mul, Nat.mul_add]
        omega
      rw [hfactor] at hbody
      simpa [binaryFormulaCode] using
        (header_payload_le_factor_mul
          (factor := uniformRewritingFormulaFactor codeBound symbolBound
            (formulaSymbolCount (∀⁰ body)))
          (header := (binaryNatCode 6).length)
          ((four_le_uniformRewritingFormulaFactor
            (formulaSymbols := formulaSymbolCount (∀⁰ body))
            hcode).trans' (by omega)) hbody)
  | hexs body ih =>
      intro targetArity codeBound symbolBound rewriting hcode hsymbol hbound
      have hq := hbound.q hcode hsymbol
      have hbody := ih rewriting.q (by omega) hsymbol hq
      have hfactor :
          uniformRewritingFormulaFactor
              (codeBound + 2 * symbolBound) symbolBound
              (formulaSymbolCount body) =
            uniformRewritingFormulaFactor codeBound symbolBound
              (formulaSymbolCount (∃⁰ body)) := by
        simp [uniformRewritingFormulaFactor, formulaSymbolCount,
          Nat.add_mul, Nat.mul_add]
        omega
      rw [hfactor] at hbody
      simpa [binaryFormulaCode] using
        (header_payload_le_factor_mul
          (factor := uniformRewritingFormulaFactor codeBound symbolBound
            (formulaSymbolCount (∃⁰ body)))
          (header := (binaryNatCode 7).length)
          ((four_le_uniformRewritingFormulaFactor
            (formulaSymbols := formulaSymbolCount (∃⁰ body))
            hcode).trans' (by omega)) hbody)

def uniformRewritingFormulaCodeEnvelope
    (imageBound formulaCodeBound : Nat) : Nat :=
  (imageBound + 4 + 2 * formulaCodeBound * (imageBound + 1)) *
    formulaCodeBound

theorem uniformRewritingFormulaCodeEnvelope_mono_formula
    (imageBound : Nat) {small large : Nat} (hbound : small <= large) :
    uniformRewritingFormulaCodeEnvelope imageBound small <=
      uniformRewritingFormulaCodeEnvelope imageBound large := by
  unfold uniformRewritingFormulaCodeEnvelope
  exact Nat.mul_le_mul
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right (imageBound + 1)
        (Nat.mul_le_mul_left 2 hbound))
      (imageBound + 4))
    hbound

theorem binaryFormulaCode_rewriting_length_le_uniform
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (imageBound : Nat)
    (hbound : RewritingImageCodeBound rewriting imageBound)
    (formula : ArithmeticSemiformula Nat sourceArity) :
    (binaryFormulaCode (rewriting ▹ formula)).length <=
      uniformRewritingFormulaCodeEnvelope imageBound
        (binaryFormulaCode formula).length := by
  have hraw := binaryFormulaCode_rewriting_length_le_factor formula rewriting
    (show 4 <= imageBound + 4 by omega)
    (show 1 <= imageBound + 1 by omega)
    (UniformRewritingImageBound.ofCodeBound hbound)
  have hsymbols := formulaSymbolCount_le_binaryFormulaCode_length formula
  unfold uniformRewritingFormulaCodeEnvelope
  exact hraw.trans (Nat.mul_le_mul_right _ (by
    unfold uniformRewritingFormulaFactor
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right (imageBound + 1)
        (Nat.mul_le_mul_left 2 hsymbols)) (imageBound + 4)))

#print axioms UniformRewritingImageBound.q
#print axioms binaryTermCode_rewriting_length_le_uniform
#print axioms binaryFormulaCode_rewriting_length_le_factor
#print axioms uniformRewritingFormulaCodeEnvelope_mono_formula
#print axioms binaryFormulaCode_rewriting_length_le_uniform

end FoundationCompactSyntaxUniformRewritingCodeBounds
