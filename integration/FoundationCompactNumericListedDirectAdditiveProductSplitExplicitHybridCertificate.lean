import integration.FoundationCompactNumericListedDirectAdditiveTypeLayouts
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-!
# Explicit hybrid certificate for additive product splits

The certificate consumes the three inequalities of the public product-split
graph directly.  No semantic truth compiler or existential choice is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectAdditiveTypeLayouts

private abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

noncomputable def closedLtCertificate
    (left right : Nat) (hlt : left < right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) <
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

noncomputable def closedLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” := by
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

def compactAdditiveProductSplitClosedFormula
    (tokenCount start middle finish : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveProductSplitDef.val) ⇜
    ![shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm middle,
      shortBinaryNumeralTerm finish]

theorem compactAdditiveProductSplitClosedFormula_alignment
    (tokenCount start middle finish : Nat) :
    compactAdditiveProductSplitClosedFormula tokenCount start middle finish =
      (“!!(shortBinaryNumeralTerm start) <
          !!(shortBinaryNumeralTerm middle)” ⋏
        (“!!(shortBinaryNumeralTerm middle) <
            !!(shortBinaryNumeralTerm finish)” ⋏
          “!!(shortBinaryNumeralTerm finish) ≤
            !!(shortBinaryNumeralTerm tokenCount)”)) := by
  unfold compactAdditiveProductSplitClosedFormula
  unfold compactAdditiveProductSplitDef
  simp

noncomputable def compactAdditiveProductSplitExplicitHybridCertificateOfGraph
    (tokenCount start middle finish : Nat)
    (hgraph : CompactAdditiveProductSplit tokenCount start middle finish) :
    HybridCertificate zeroValuation
      (compactAdditiveProductSplitClosedFormula
        tokenCount start middle finish) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLtCertificate start middle hgraph.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLtCertificate middle finish hgraph.2.1)
      (closedLeCertificate finish tokenCount hgraph.2.2))
  exact .cast
    (compactAdditiveProductSplitClosedFormula_alignment
      tokenCount start middle finish).symm parts

#print axioms compactAdditiveProductSplitClosedFormula_alignment
#print axioms compactAdditiveProductSplitExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
