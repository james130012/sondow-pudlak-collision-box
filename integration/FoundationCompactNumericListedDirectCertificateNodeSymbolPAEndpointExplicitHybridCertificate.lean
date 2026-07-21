import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for a symbol PA-axiom certificate node

This is a direct certificate for the original twenty-seven-coordinate
SymbolPA endpoint formula.  In particular, the two finite symbol-code domains
are represented by their original equality disjunctions.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpointExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactArithmeticSymbolCode
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev SymbolPAEndpointHybridCertificate
    (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_emptyFormulaSubstitution
    {targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity -> ArithmeticSemiterm Empty sourceArity) :
    rewriting ▹ (formula ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      rewriting.comp (Rew.subst terms) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ (formula ⇜ terms) =
        (rewriting.comp (Rew.subst terms)) ▹ formula := by
      rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private def symbolPAEndpointOuterTerms
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    Fin 27 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm axiomStart,
    shortBinaryNumeralTerm axiomFinish,
    shortBinaryNumeralTerm suffixStart,
    shortBinaryNumeralTerm suffixFinish,
    shortBinaryNumeralTerm certificateTag,
    shortBinaryNumeralTerm coordinates.inputBoundary,
    shortBinaryNumeralTerm coordinates.inputCount,
    shortBinaryNumeralTerm coordinates.inputBoundarySize,
    shortBinaryNumeralTerm coordinates.tailStart,
    shortBinaryNumeralTerm coordinates.tailFinish,
    shortBinaryNumeralTerm coordinates.tailBoundary,
    shortBinaryNumeralTerm coordinates.tailCount,
    shortBinaryNumeralTerm coordinates.tailBoundarySize,
    shortBinaryNumeralTerm coordinates.axiomBoundary,
    shortBinaryNumeralTerm coordinates.axiomCount,
    shortBinaryNumeralTerm coordinates.axiomBoundarySize,
    shortBinaryNumeralTerm coordinates.suffixBoundary,
    shortBinaryNumeralTerm coordinates.suffixCount,
    shortBinaryNumeralTerm coordinates.suffixBoundarySize,
    shortBinaryNumeralTerm coordinates.paTag,
    shortBinaryNumeralTerm coordinates.arity,
    shortBinaryNumeralTerm coordinates.symbolCode]

/-- The original SymbolPA endpoint graph with every public coordinate closed. -/
def compactCertificateNodeSymbolPAEndpointClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSymbolPAEndpointGraphDef.val) ⇜
    symbolPAEndpointOuterTerms tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag coordinates

private def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

private def fixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

private def funcCodeValidFormula (arity code : Nat) : ValuationFormula :=
  (fixedEqFormula arity 0 ⋏ fixedEqFormula code 0) ⋎
    (fixedEqFormula arity 0 ⋏ fixedEqFormula code 1) ⋎
    (fixedEqFormula arity 2 ⋏ fixedEqFormula code 0) ⋎
    (fixedEqFormula arity 2 ⋏ fixedEqFormula code 1)

private def relCodeValidFormula (arity code : Nat) : ValuationFormula :=
  (fixedEqFormula arity 2 ⋏ fixedEqFormula code 0) ⋎
    (fixedEqFormula arity 2 ⋏ fixedEqFormula code 1)

private def compactCertificateNodeSymbolPAEndpointExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    ValuationFormula :=
  let inputRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount inputStart coordinates.inputCount inputFinish
      coordinates.inputBoundary coordinates.inputBoundarySize
  let tailRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount coordinates.tailStart coordinates.tailCount
      coordinates.tailFinish coordinates.tailBoundary coordinates.tailBoundarySize
  let axiomRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount axiomStart coordinates.axiomCount axiomFinish
      coordinates.axiomBoundary coordinates.axiomBoundarySize
  let suffixRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount suffixStart coordinates.suffixCount suffixFinish
      coordinates.suffixBoundary coordinates.suffixBoundarySize
  let outerCons := compactAdditiveNatListConsRowsAtValuationHeadFormula
    tokenTable width tokenCount coordinates.tailBoundary coordinates.tailCount
      coordinates.inputBoundary coordinates.inputCount (fixedNumeralTerm 1)
  let appendRows := compactAdditiveNatListAppendSlicesClosedFormula tokenTable
    width tokenCount axiomStart axiomFinish coordinates.axiomCount suffixStart
      suffixFinish coordinates.suffixCount coordinates.tailStart
      coordinates.tailFinish coordinates.tailCount
  let atZero := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
    width tokenCount coordinates.axiomBoundary coordinates.axiomCount
      coordinates.paTag (fixedNumeralTerm 0)
  let atOne := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
    width tokenCount coordinates.axiomBoundary coordinates.axiomCount
      coordinates.arity (fixedNumeralTerm 1)
  let atTwo := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
    width tokenCount coordinates.axiomBoundary coordinates.axiomCount
      coordinates.symbolCode (fixedNumeralTerm 2)
  inputRows ⋏ tailRows ⋏ axiomRows ⋏ suffixRows ⋏
    fixedEqFormula certificateTag 1 ⋏ fixedEqFormula coordinates.axiomCount 3 ⋏
    ((fixedEqFormula coordinates.paTag 3 ⋏
        funcCodeValidFormula coordinates.arity coordinates.symbolCode) ⋎
      (fixedEqFormula coordinates.paTag 4 ⋏
        relCodeValidFormula coordinates.arity coordinates.symbolCode)) ⋏
    outerCons ⋏ appendRows ⋏ atZero ⋏ atOne ⋏ atTwo

theorem compactCertificateNodeSymbolPAEndpointClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    compactCertificateNodeSymbolPAEndpointClosedFormula tokenTable width tokenCount
        inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish
        certificateTag coordinates =
      compactCertificateNodeSymbolPAEndpointExplicitFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
        suffixFinish certificateTag coordinates := by
  unfold compactCertificateNodeSymbolPAEndpointClosedFormula
    compactCertificateNodeSymbolPAEndpointExplicitFormula
    funcCodeValidFormula relCodeValidFormula fixedEqFormula fixedNumeralTerm
    symbolPAEndpointOuterTerms compactCertificateNodeSymbolPAEndpointGraphDef
    compactAdditiveArithmeticFuncCodeValidDef
    compactAdditiveArithmeticRelCodeValidDef
    compactAdditiveNatListWitnessRowsClosedFormula
    compactAdditiveNatListAppendSlicesClosedFormula
    compactAdditiveNatListAtRowsAtValuationIndexFormula
  rw [compactAdditiveNatListConsRowsAtValuationHeadFormula_eq_explicitSubstitution]
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution, Rew.subst_bvar]
  repeat' apply And.intro
  all_goals
    congr 1 <;>
      try
        (funext coordinate
         fin_cases coordinate <;> simp [Rew.subst_bvar] <;> rfl)
  all_goals
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply, Rew.subst_bvar] <;> rfl

@[simp] private theorem termValue_fixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  rw [LO.FirstOrder.Structure.numeral_eq_numeral
    (L := ℒₒᵣ) (M := Nat) value]
  simp

private noncomputable def fixedEqCertificate
    (value expected : Nat) (heq : value = expected) :
    SymbolPAEndpointHybridCertificate (fixedEqFormula value expected) := by
  unfold fixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

private theorem funcCodeValidCertificate_nonempty
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    Nonempty
      (SymbolPAEndpointHybridCertificate
        (funcCodeValidFormula arity code)) := by
  unfold ArithmeticFuncCodeValid at hvalid
  rcases hvalid with hvalid | hvalid | hvalid | hvalid
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (fixedEqCertificate arity 0 hvalid.1)
        (fixedEqCertificate code 0 hvalid.2))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (fixedEqCertificate arity 0 hvalid.1)
          (fixedEqCertificate code 1 hvalid.2)))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedEqCertificate arity 2 hvalid.1)
            (fixedEqCertificate code 0 hvalid.2))))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedEqCertificate arity 2 hvalid.1)
            (fixedEqCertificate code 1 hvalid.2))))⟩

private noncomputable def funcCodeValidCertificate
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    SymbolPAEndpointHybridCertificate (funcCodeValidFormula arity code) :=
  Classical.choice (funcCodeValidCertificate_nonempty arity code hvalid)

private theorem relCodeValidCertificate_nonempty
    (arity code : Nat) (hvalid : ArithmeticRelCodeValid arity code) :
    Nonempty
      (SymbolPAEndpointHybridCertificate
        (relCodeValidFormula arity code)) := by
  unfold ArithmeticRelCodeValid at hvalid
  rcases hvalid with hvalid | hvalid
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (fixedEqCertificate arity 2 hvalid.1)
        (fixedEqCertificate code 0 hvalid.2))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (fixedEqCertificate arity 2 hvalid.1)
        (fixedEqCertificate code 1 hvalid.2))⟩

private noncomputable def relCodeValidCertificate
    (arity code : Nat) (hvalid : ArithmeticRelCodeValid arity code) :
    SymbolPAEndpointHybridCertificate (relCodeValidFormula arity code) :=
  Classical.choice (relCodeValidCertificate_nonempty arity code hvalid)

/-- Complete checked certificate for the original SymbolPA endpoint graph. -/
noncomputable def
    compactCertificateNodeSymbolPAEndpointExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates)
    (hgraph : CompactCertificateNodeSymbolPAEndpointGraph tokenTable width
      tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
      suffixFinish certificateTag coordinates) :
    SymbolPAEndpointHybridCertificate
      (compactCertificateNodeSymbolPAEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
        suffixFinish certificateTag coordinates) := by
  rw [compactCertificateNodeSymbolPAEndpointClosedFormula_alignment]
  unfold compactCertificateNodeSymbolPAEndpointExplicitFormula
  rcases hgraph with
    ⟨hinput, htail, haxiom, hsuffix, hcertificateTag, haxiomCount,
      hvalid, houterCons, happend, hatZero, hatOne, hatTwo⟩
  let symbolCertificate : SymbolPAEndpointHybridCertificate
      ((fixedEqFormula coordinates.paTag 3 ⋏
          funcCodeValidFormula coordinates.arity coordinates.symbolCode) ⋎
        (fixedEqFormula coordinates.paTag 4 ⋏
          relCodeValidFormula coordinates.arity coordinates.symbolCode)) :=
    Classical.choice (show Nonempty
        (SymbolPAEndpointHybridCertificate
          ((fixedEqFormula coordinates.paTag 3 ⋏
              funcCodeValidFormula coordinates.arity coordinates.symbolCode) ⋎
            (fixedEqFormula coordinates.paTag 4 ⋏
              relCodeValidFormula coordinates.arity coordinates.symbolCode))) from by
      rcases hvalid with ⟨hpaTag, hfunc⟩ | ⟨hpaTag, hrel⟩
      · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedEqCertificate coordinates.paTag 3 hpaTag)
            (funcCodeValidCertificate coordinates.arity
              coordinates.symbolCode hfunc))⟩
      · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedEqCertificate coordinates.paTag 4 hpaTag)
            (relCodeValidCertificate coordinates.arity
              coordinates.symbolCode hrel))⟩)
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
      coordinates.inputBoundary coordinates.inputBoundarySize hinput)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount coordinates.tailStart coordinates.tailCount
        coordinates.tailFinish coordinates.tailBoundary coordinates.tailBoundarySize htail)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount axiomStart coordinates.axiomCount axiomFinish
          coordinates.axiomBoundary coordinates.axiomBoundarySize haxiom)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount suffixStart coordinates.suffixCount suffixFinish
            coordinates.suffixBoundary coordinates.suffixBoundarySize hsuffix)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedEqCertificate certificateTag 1 hcertificateTag)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (fixedEqCertificate coordinates.axiomCount 3 haxiomCount)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                symbolCertificate
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactAdditiveNatListConsRowsAtValuationHeadExplicitHybridCertificateOfGraph
                    tokenTable width tokenCount coordinates.tailBoundary
                    coordinates.tailCount coordinates.inputBoundary coordinates.inputCount
                    1 (fixedNumeralTerm 1) (by simp) houterCons)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount axiomStart axiomFinish
                      coordinates.axiomCount suffixStart suffixFinish
                      coordinates.suffixCount coordinates.tailStart
                      coordinates.tailFinish coordinates.tailCount happend)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                        tokenTable width tokenCount coordinates.axiomBoundary
                        coordinates.axiomCount 0 coordinates.paTag
                          (fixedNumeralTerm 0) (by simp) hatZero)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                          tokenTable width tokenCount coordinates.axiomBoundary
                          coordinates.axiomCount 1 coordinates.arity
                            (fixedNumeralTerm 1) (by simp) hatOne)
                        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                          tokenTable width tokenCount coordinates.axiomBoundary
                          coordinates.axiomCount 2 coordinates.symbolCode
                            (fixedNumeralTerm 2) (by simp) hatTwo)))))))))))

#print axioms compactCertificateNodeSymbolPAEndpointClosedFormula_alignment
#print axioms compactCertificateNodeSymbolPAEndpointExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpointExplicitHybridCertificate
