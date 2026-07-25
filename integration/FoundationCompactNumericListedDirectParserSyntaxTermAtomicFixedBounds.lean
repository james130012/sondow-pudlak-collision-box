import integration.FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

/-! # Fixed atomic resources for the Term parser's own certificate family -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

theorem syntaxTermNativeEqCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (heq : value = expected)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 7) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeEqCertificate
          value expected heq) <=
      parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound := by
  change compilePositiveRelationPayloadResource termZeroValuation
      Language.Eq.eq ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] <=
    _
  unfold parserFormulaPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    termZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) (fixedNumeralTerm expected)
    0 (parserFormulaAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (parserFormulaFixedNumeral_freeVariables_eq_empty expected)
    (parserFormulaShortNumeralCode_le value bitBound hvalueSize)
    (parserFormulaFixedTagCode_le expected bitBound hexpected)

theorem syntaxTermNativeNeCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (hne : value ≠ expected)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 7) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeNeCertificate
          value expected hne) <=
      parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound := by
  change compileNegativeRelationPayloadResource termZeroValuation
      Language.Eq.eq ![shortBinaryNumeralTerm value,
        fixedNumeralTerm expected] <= _
  unfold parserFormulaNegativeAtomicFixedPayloadPolynomial
  exact compileNegativeRelationPayloadResource_le_fixed_of_closed
    termZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) (fixedNumeralTerm expected)
    0 (parserFormulaAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (parserFormulaFixedNumeral_freeVariables_eq_empty expected)
    (parserFormulaShortNumeralCode_le value bitBound hvalueSize)
    (parserFormulaFixedTagCode_le expected bitBound hexpected)

theorem syntaxTermShortLtCertificate_structuralPayloadBound_le_fixed
    (left right bitBound : Nat)
    (hlt : left < right)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLtCertificate
          left right hlt) <=
      parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound := by
  change compilePositiveRelationPayloadResource termZeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] <= _
  unfold parserFormulaPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    termZeroValuation Language.ORing.Rel.lt
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
    0 (parserFormulaAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (parserFormulaShortNumeralCode_le left bitBound hleftSize)
    (parserFormulaShortNumeralCode_le right bitBound hrightSize)

theorem syntaxTermShortLeCertificate_structuralPayloadBound_le_fixed
    (left right bitBound : Nat)
    (hle : left <= right)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLeCertificate
          left right hle) <=
      parserFormulaTermLeFixedPayloadPolynomial bitBound := by
  let formulaZeroValuation :=
    FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
  have hleftValue :
      termValue formulaZeroValuation (shortBinaryNumeralTerm left) = left := by
    simp [formulaZeroValuation, termValue_shortBinaryNumeralTerm]
  have hrightValue :
      termValue formulaZeroValuation (shortBinaryNumeralTerm right) = right := by
    simp [formulaZeroValuation, termValue_shortBinaryNumeralTerm]
  have hsource :=
    FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds.termLeCertificate_structuralPayloadBound_le_fixed
      left right (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
      bitBound
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (parserFormulaShortNumeralCode_le left bitBound hleftSize)
      (parserFormulaShortNumeralCode_le right bitBound hrightSize)
      hleftValue hrightValue hle
  have hcertificate :
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLeCertificate
          left right hle =
        FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.termLeCertificate
          left right (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm right) hleftValue hrightValue hle := by
    unfold
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLeFormula
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeFormula
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.termLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.termLeFormula
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
    rfl
  rw [hcertificate]
  exact hsource

theorem syntaxTermNativeShortLeCertificate_structuralPayloadBound_le_fixed
    (left right bitBound : Nat) (hle : left <= right)
    (hleft : left <= 7)
    (hrightSize : Nat.size right <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeShortLeCertificate
          left right hle) <=
      parserFormulaTermLeFixedPayloadPolynomial bitBound := by
  have hsource :=
    FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds.nativeShortLeCertificate_structuralPayloadBound_le_fixed
      left right bitBound hle hleft hrightSize
  have hcertificate :
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeShortLeCertificate
          left right hle =
        FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.nativeShortLeCertificate
          left right hle := by
    unfold
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeShortLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeShortLeFormula
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeFormula
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.nativeShortLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.nativeShortLeFormula
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.termLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.termLeFormula
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
    rfl
  rw [hcertificate]
  exact hsource

theorem syntaxTermShortNativeLeCertificate_structuralPayloadBound_le_fixed
    (left right bitBound : Nat) (hle : left <= right)
    (hleftSize : Nat.size left <= bitBound)
    (hright : right <= 7) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortNativeLeCertificate
          left right hle) <=
      parserFormulaTermLeFixedPayloadPolynomial bitBound := by
  have hsource :=
    FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds.shortNativeLeCertificate_structuralPayloadBound_le_fixed
      left right bitBound hle hleftSize hright
  have hcertificate :
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortNativeLeCertificate
          left right hle =
        FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.shortNativeLeCertificate
          left right hle := by
    unfold
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortNativeLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortNativeLeFormula
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeFormula
      FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.shortNativeLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.shortNativeLeFormula
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.termLeCertificate
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.termLeFormula
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
    rfl
  rw [hcertificate]
  exact hsource

theorem syntaxTermShortNativeLeFormula_freeVariables_eq_empty
    (left right : Nat) :
    (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortNativeLeFormula
      left right).freeVariables = ∅ := by
  unfold
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortNativeLeFormula
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeFormula
  rw [LO.FirstOrder.Semiformula.Operator.le_def,
    LO.FirstOrder.Semiformula.freeVariables_or]
  have heq := parserFormulaBinaryRelation_freeVariables_eq_empty Language.Eq.eq
    (shortBinaryNumeralTerm left) (fixedNumeralTerm right)
    (shortBinaryNumeralTerm_freeVariables_eq_empty left)
    (parserFormulaFixedNumeral_freeVariables_eq_empty right)
  have hlt := parserFormulaBinaryRelation_freeVariables_eq_empty Language.LT.lt
    (shortBinaryNumeralTerm left) (fixedNumeralTerm right)
    (shortBinaryNumeralTerm_freeVariables_eq_empty left)
    (parserFormulaFixedNumeral_freeVariables_eq_empty right)
  rw [heq, hlt]
  simp

theorem syntaxTermNativeShortLeFormula_freeVariables_eq_empty
    (left right : Nat) :
    (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeShortLeFormula
      left right).freeVariables = ∅ := by
  unfold
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeShortLeFormula
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeFormula
  rw [LO.FirstOrder.Semiformula.Operator.le_def,
    LO.FirstOrder.Semiformula.freeVariables_or]
  have heq := parserFormulaBinaryRelation_freeVariables_eq_empty Language.Eq.eq
    (fixedNumeralTerm left) (shortBinaryNumeralTerm right)
    (parserFormulaFixedNumeral_freeVariables_eq_empty left)
    (shortBinaryNumeralTerm_freeVariables_eq_empty right)
  have hlt := parserFormulaBinaryRelation_freeVariables_eq_empty Language.LT.lt
    (fixedNumeralTerm left) (shortBinaryNumeralTerm right)
    (parserFormulaFixedNumeral_freeVariables_eq_empty left)
    (shortBinaryNumeralTerm_freeVariables_eq_empty right)
  rw [heq, hlt]
  simp

theorem syntaxTermNativeEqFormula_freeVariables_eq_empty
    (value expected : Nat) :
    (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeEqFormula
      value expected).freeVariables = ∅ := by
  unfold
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeEqFormula
  exact parserFormulaBinaryRelation_freeVariables_eq_empty Language.Eq.eq
    (shortBinaryNumeralTerm value) (fixedNumeralTerm expected)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (parserFormulaFixedNumeral_freeVariables_eq_empty expected)

theorem syntaxTermNativeNeFormula_freeVariables_eq_empty
    (value expected : Nat) :
    (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeNeFormula
      value expected).freeVariables = ∅ := by
  unfold
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.nativeNeFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_not,
    syntaxTermNativeEqFormula_freeVariables_eq_empty]

theorem syntaxTermShortLtFormula_freeVariables_eq_empty
    (left right : Nat) :
    (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLtFormula
      left right).freeVariables = ∅ := by
  unfold
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLtFormula
  exact parserFormulaBinaryRelation_freeVariables_eq_empty Language.ORing.Rel.lt
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)

theorem syntaxTermShortLeFormula_freeVariables_eq_empty
    (left right : Nat) :
    (FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLeFormula
      left right).freeVariables = ∅ := by
  unfold
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.shortLeFormula
    FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.termLeFormula
  rw [LO.FirstOrder.Semiformula.Operator.le_def,
    LO.FirstOrder.Semiformula.freeVariables_or]
  have heq := parserFormulaBinaryRelation_freeVariables_eq_empty
    Language.Eq.eq (shortBinaryNumeralTerm left)
    (shortBinaryNumeralTerm right)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hlt := parserFormulaBinaryRelation_freeVariables_eq_empty
    Language.LT.lt (shortBinaryNumeralTerm left)
    (shortBinaryNumeralTerm right)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  rw [heq, hlt]
  simp

#print axioms syntaxTermNativeEqCertificate_structuralPayloadBound_le_fixed
#print axioms syntaxTermNativeNeCertificate_structuralPayloadBound_le_fixed
#print axioms syntaxTermShortLtCertificate_structuralPayloadBound_le_fixed
#print axioms syntaxTermShortLeCertificate_structuralPayloadBound_le_fixed
#print axioms syntaxTermNativeShortLeCertificate_structuralPayloadBound_le_fixed
#print axioms syntaxTermShortNativeLeCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds
