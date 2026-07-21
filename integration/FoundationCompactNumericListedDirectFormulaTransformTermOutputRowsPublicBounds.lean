import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

/-!
# Public structural resources for formula-transform term output rows

The fourteen checked branches are represented by explicit branch data.  Each
failure choice, residual witness, and child row graph is charged by its actual
transparent certificate; no payload resource is accepted from the caller.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds

private abbrev termRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticZeroTerm_freeVariables_eq_empty :
    (‘0’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq]

private theorem termRowsArithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem nativeAddTerm_freeVariables_eq_empty
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (nativeAddTerm left right).freeVariables = ∅ := by
  unfold nativeAddTerm
  rw [termRowsArithmeticAddTerm_eq_func]
  rw [binaryFunctionTerm_freeVariables, hleft, hright]
  simp

def termRowsNativeEqStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource termRowsZeroValuation
    Language.Eq.eq ![left, right]

theorem nativeEqCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hequal : termValue termRowsZeroValuation left =
      termValue termRowsZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (nativeEqCertificate left right hequal) <=
      termRowsNativeEqStructuralEnvelope left right := by
  simp only [nativeEqCertificate, termRowsNativeEqStructuralEnvelope]
  exact le_rfl

def termRowsNativeNeStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  compileNegativeRelationPayloadResource termRowsZeroValuation
    Language.Eq.eq ![left, right]

theorem nativeNeCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hne : termValue termRowsZeroValuation left ≠
      termValue termRowsZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (nativeNeCertificate left right hne) <=
      termRowsNativeNeStructuralEnvelope left right := by
  simp only [nativeNeCertificate, termRowsNativeNeStructuralEnvelope]
  exact le_rfl

def termRowsNativeLtStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource termRowsZeroValuation
    Language.ORing.Rel.lt ![left, right]

theorem nativeLtCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hlt : termValue termRowsZeroValuation left <
      termValue termRowsZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (nativeLtCertificate left right hlt) <=
      termRowsNativeLtStructuralEnvelope left right := by
  simp only [nativeLtCertificate, termRowsNativeLtStructuralEnvelope]
  exact le_rfl

def termRowsNativeLeStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![left, right]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    termRowsZeroValuation
  compilePositiveRelationPayloadResource termRowsZeroValuation
      Language.Eq.eq args +
    compilePositiveRelationPayloadResource termRowsZeroValuation
      Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem nativeLeCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hle : termValue termRowsZeroValuation left <=
      termValue termRowsZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (nativeLeCertificate left right hle) <=
      termRowsNativeLeStructuralEnvelope left right := by
  let args : Fin 2 -> ValuationTerm := ![left, right]
  by_cases hequal : termValue termRowsZeroValuation left =
      termValue termRowsZeroValuation right
  · simp only [nativeLeCertificate, nativeLeCertificateCore, nativeLeFormula]
    rw [dif_pos hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold termRowsNativeLeStructuralEnvelope
    dsimp only [args, termRowsZeroValuation]
    omega
  · simp only [nativeLeCertificate, nativeLeCertificateCore, nativeLeFormula]
    rw [dif_neg hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold termRowsNativeLeStructuralEnvelope
    dsimp only [args, termRowsZeroValuation]
    omega

theorem shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
    (value expected : Nat) (literal : ValuationTerm)
    (hliteral : termValue termRowsZeroValuation literal = expected)
    (heq : value = expected) :
    hybridFormulaStructuralPayloadBound
        (shortNumeralLiteralEqCertificate value expected literal hliteral heq) <=
      termRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm value) literal := by
  have hequal : termValue termRowsZeroValuation
      (shortBinaryNumeralTerm value) =
        termValue termRowsZeroValuation literal := by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using heq
  simpa only [shortNumeralLiteralEqCertificate] using
    nativeEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm value) literal hequal

theorem shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent
    (value expected : Nat) (literal : ValuationTerm)
    (hliteral : termValue termRowsZeroValuation literal = expected)
    (hne : value ≠ expected) :
    hybridFormulaStructuralPayloadBound
        (shortNumeralLiteralNeCertificate value expected literal hliteral hne) <=
      termRowsNativeNeStructuralEnvelope
        (shortBinaryNumeralTerm value) literal := by
  have hunequal : termValue termRowsZeroValuation
      (shortBinaryNumeralTerm value) ≠
        termValue termRowsZeroValuation literal := by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using hne
  simpa only [shortNumeralLiteralNeCertificate] using
    nativeNeCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm value) literal hunequal

theorem consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount) :
    hybridFormulaStructuralPayloadBound
        (consumedCountEqualityCertificate current next consumedCount hcount) <=
      termRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)) := by
  have hequal : termValue termRowsZeroValuation
      (shortBinaryNumeralTerm current.parserTokensCount) =
        termValue termRowsZeroValuation
          (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm next.parserTokensCount)) := by
    simpa [termValue_shortBinaryNumeralTerm, nativeAddTerm,
      termValue_arithmeticAdd] using hcount
  simpa only [consumedCountEqualityCertificate] using
    nativeEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount)) hequal

theorem consumedCountZeroCertificate_structuralPayloadBound_le_transparent
    (consumedCount : Nat) (hzero : consumedCount = 0) :
    hybridFormulaStructuralPayloadBound
        (consumedCountZeroCertificate consumedCount hzero) <=
      termRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm) := by
  have hequal : termValue termRowsZeroValuation
      (shortBinaryNumeralTerm consumedCount) =
        termValue termRowsZeroValuation (‘0’ : ValuationTerm) := by
    simpa [termValue_shortBinaryNumeralTerm,
      termValue_arithmeticZero] using hzero
  simpa only [consumedCountZeroCertificate,
    shortNumeralLiteralEqCertificate] using
    nativeEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm) hequal

theorem consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
    (consumedCount : Nat) (hpositive : 1 <= consumedCount) :
    hybridFormulaStructuralPayloadBound
        (consumedCountPositiveCertificate consumedCount hpositive) <=
      termRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount) := by
  have hle : termValue termRowsZeroValuation (‘1’ : ValuationTerm) <=
      termValue termRowsZeroValuation
        (shortBinaryNumeralTerm consumedCount) := by
    simpa [termValue_arithmeticOne,
      termValue_shortBinaryNumeralTerm] using hpositive
  simpa only [consumedCountPositiveCertificate] using
    nativeLeCertificate_structuralPayloadBound_le_transparent
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm consumedCount) hle

def zeroTagGuardPayloadEnvelope
    (consumedCount tag argument binderArity : Nat) : Nat :=
  let consumedFormula := nativeEqFormula
    (shortBinaryNumeralTerm consumedCount) (‘2’ : ValuationTerm)
  let tagFormula := nativeEqFormula
    (shortBinaryNumeralTerm tag) (‘0’ : ValuationTerm)
  let argumentFormula := nativeEqFormula
    (nativeAddTerm (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm))
    (shortBinaryNumeralTerm binderArity)
  let tagArgument := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation tagFormula argumentFormula
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm tag) (‘0’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope
      (nativeAddTerm (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm))
      (shortBinaryNumeralTerm binderArity))
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    consumedFormula (tagFormula ⋏ argumentFormula)
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm consumedCount) (‘2’ : ValuationTerm))
    tagArgument

theorem zeroTagGuardCertificate_structuralPayloadBound_le_transparent
    (consumedCount tag argument binderArity : Nat)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity) :
    hybridFormulaStructuralPayloadBound
        (zeroTagGuardCertificate consumedCount tag argument binderArity
          hguard) <=
      zeroTagGuardPayloadEnvelope consumedCount tag argument binderArity := by
  let consumedCertificate := shortNumeralLiteralEqCertificate consumedCount 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo termRowsZeroValuation)
    hguard.1
  let tagCertificate := shortNumeralLiteralEqCertificate tag 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero termRowsZeroValuation)
    hguard.2.1
  let argumentCertificate := nativeEqCertificate
    (nativeAddTerm (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm))
    (shortBinaryNumeralTerm binderArity) (by
      simpa [nativeAddTerm, termValue_arithmeticAdd,
        termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]
        using hguard.2.2)
  have hconsumed :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo termRowsZeroValuation) hguard.1
  have htag :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      tag 0 (‘0’ : ValuationTerm)
      (termValue_arithmeticZero termRowsZeroValuation) hguard.2.1
  have hargument :=
    nativeEqCertificate_structuralPayloadBound_le_transparent
      (nativeAddTerm (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm))
      (shortBinaryNumeralTerm binderArity) (by
        simpa [nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]
          using hguard.2.2)
  let tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    tagCertificate argumentCertificate
  have htail := transparentHybridConjunctionPayloadBound_le tagCertificate
    argumentCertificate _ _ htag hargument
  have hall := transparentHybridConjunctionPayloadBound_le consumedCertificate
    tail _ _ hconsumed htail
  simpa only [zeroTagGuardCertificate, zeroTagGuardPayloadEnvelope,
    consumedCertificate, tagCertificate, argumentCertificate, tail] using hall

def oneTagGuardPayloadEnvelope (consumedCount tag : Nat) : Nat :=
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘2’ : ValuationTerm))
    (nativeEqFormula (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm consumedCount) (‘2’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm))

theorem oneTagGuardCertificate_structuralPayloadBound_le_transparent
    (consumedCount tag : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1) :
    hybridFormulaStructuralPayloadBound
        (oneTagGuardCertificate consumedCount tag hguard) <=
      oneTagGuardPayloadEnvelope consumedCount tag := by
  let consumedCertificate := shortNumeralLiteralEqCertificate consumedCount 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo termRowsZeroValuation)
    hguard.1
  let tagCertificate := shortNumeralLiteralEqCertificate tag 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne termRowsZeroValuation)
    hguard.2
  have hconsumed :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo termRowsZeroValuation) hguard.1
  have htag :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      tag 1 (‘1’ : ValuationTerm)
      (termValue_arithmeticOne termRowsZeroValuation) hguard.2
  have hall := transparentHybridConjunctionPayloadBound_le consumedCertificate
    tagCertificate _ _ hconsumed htag
  simpa only [oneTagGuardCertificate, oneTagGuardPayloadEnvelope,
    consumedCertificate, tagCertificate] using hall

def capturedGuardPayloadEnvelope
    (consumedCount tag argument witnessCount : Nat) : Nat :=
  let consumedFormula := nativeEqFormula
    (shortBinaryNumeralTerm consumedCount) (‘2’ : ValuationTerm)
  let tagFormula := nativeEqFormula
    (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm)
  let comparisonFormula := nativeLtFormula
    (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm witnessCount)
  let tail := transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    tagFormula comparisonFormula
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm))
    (termRowsNativeLtStructuralEnvelope
      (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm witnessCount))
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    consumedFormula (tagFormula ⋏ comparisonFormula)
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm consumedCount) (‘2’ : ValuationTerm)) tail

theorem capturedGuardCertificate_structuralPayloadBound_le_transparent
    (consumedCount tag argument witnessCount : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount) :
    hybridFormulaStructuralPayloadBound
        (capturedGuardCertificate consumedCount tag argument witnessCount
          hguard) <=
      capturedGuardPayloadEnvelope consumedCount tag argument witnessCount := by
  let consumedCertificate := shortNumeralLiteralEqCertificate consumedCount 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo termRowsZeroValuation)
    hguard.1
  let tagCertificate := shortNumeralLiteralEqCertificate tag 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne termRowsZeroValuation)
    hguard.2.1
  let comparisonCertificate := nativeLtCertificate
    (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm witnessCount) (by
      simpa [termValue_shortBinaryNumeralTerm] using hguard.2.2)
  have hconsumed :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo termRowsZeroValuation) hguard.1
  have htag :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      tag 1 (‘1’ : ValuationTerm)
      (termValue_arithmeticOne termRowsZeroValuation) hguard.2.1
  have hcomparison := nativeLtCertificate_structuralPayloadBound_le_transparent
    (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm witnessCount) (by
      simpa [termValue_shortBinaryNumeralTerm] using hguard.2.2)
  let tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    tagCertificate comparisonCertificate
  have htail := transparentHybridConjunctionPayloadBound_le tagCertificate
    comparisonCertificate _ _ htag hcomparison
  have hall := transparentHybridConjunctionPayloadBound_le consumedCertificate
    tail _ _ hconsumed htail
  simpa only [capturedGuardCertificate, capturedGuardPayloadEnvelope,
    consumedCertificate, tagCertificate, comparisonCertificate, tail] using
    hall

def residualGuardPayloadEnvelope
    (consumedCount tag argument witnessCount : Nat) : Nat :=
  let consumedFormula := nativeEqFormula
    (shortBinaryNumeralTerm consumedCount) (‘2’ : ValuationTerm)
  let tagFormula := nativeEqFormula
    (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm)
  let comparisonFormula := nativeLeFormula
    (shortBinaryNumeralTerm witnessCount) (shortBinaryNumeralTerm argument)
  let tail := transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    tagFormula comparisonFormula
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm))
    (termRowsNativeLeStructuralEnvelope
      (shortBinaryNumeralTerm witnessCount) (shortBinaryNumeralTerm argument))
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    consumedFormula (tagFormula ⋏ comparisonFormula)
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm consumedCount) (‘2’ : ValuationTerm)) tail

theorem residualGuardCertificate_structuralPayloadBound_le_transparent
    (consumedCount tag argument witnessCount : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ witnessCount <= argument) :
    hybridFormulaStructuralPayloadBound
        (residualGuardCertificate consumedCount tag argument witnessCount
          hguard) <=
      residualGuardPayloadEnvelope consumedCount tag argument witnessCount := by
  let consumedCertificate := shortNumeralLiteralEqCertificate consumedCount 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo termRowsZeroValuation)
    hguard.1
  let tagCertificate := shortNumeralLiteralEqCertificate tag 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne termRowsZeroValuation)
    hguard.2.1
  let comparisonCertificate := nativeLeCertificate
    (shortBinaryNumeralTerm witnessCount) (shortBinaryNumeralTerm argument) (by
      simpa [termValue_shortBinaryNumeralTerm] using hguard.2.2)
  have hconsumed :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo termRowsZeroValuation) hguard.1
  have htag :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      tag 1 (‘1’ : ValuationTerm)
      (termValue_arithmeticOne termRowsZeroValuation) hguard.2.1
  have hcomparison := nativeLeCertificate_structuralPayloadBound_le_transparent
    (shortBinaryNumeralTerm witnessCount) (shortBinaryNumeralTerm argument) (by
      simpa [termValue_shortBinaryNumeralTerm] using hguard.2.2)
  let tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    tagCertificate comparisonCertificate
  have htail := transparentHybridConjunctionPayloadBound_le tagCertificate
    comparisonCertificate _ _ htag hcomparison
  have hall := transparentHybridConjunctionPayloadBound_le consumedCertificate
    tail _ _ hconsumed htail
  simpa only [residualGuardCertificate, residualGuardPayloadEnvelope,
    consumedCertificate, tagCertificate, comparisonCertificate, tail] using
    hall

def tripleFailurePayloadEnvelopeFromData
    (consumedCount tag argument binderArity : Nat)
    (data : TripleFailureCheckedData consumedCount tag argument binderArity) :
    Nat :=
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let binderArityTerm := shortBinaryNumeralTerm binderArity
  let consumedFormula := nativeNeFormula consumedTerm (‘2’ : ValuationTerm)
  let tagFormula := nativeNeFormula tagTerm (‘0’ : ValuationTerm)
  let argumentFormula := nativeNeFormula
    (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm
  match data with
  | .consumed _ =>
      transparentHybridDisjunctionLeftPayloadEnvelope termRowsZeroValuation
        consumedFormula (tagFormula ⋎ argumentFormula)
        (termRowsNativeNeStructuralEnvelope consumedTerm
          (‘2’ : ValuationTerm))
  | .tag _ _ =>
      let selected := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation tagFormula argumentFormula
        (termRowsNativeNeStructuralEnvelope tagTerm (‘0’ : ValuationTerm))
      transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
        consumedFormula (tagFormula ⋎ argumentFormula) selected
  | .argument _ _ _ =>
      let selected := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation tagFormula argumentFormula
        (termRowsNativeNeStructuralEnvelope
          (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm)
      transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
        consumedFormula (tagFormula ⋎ argumentFormula) selected

theorem
    tripleFailureCertificateFromData_structuralPayloadBound_le_transparent
    (consumedCount tag argument binderArity : Nat)
    (data : TripleFailureCheckedData consumedCount tag argument binderArity) :
    hybridFormulaStructuralPayloadBound
        (tripleFailureCertificateFromData consumedCount tag argument
          binderArity data) <=
      tripleFailurePayloadEnvelopeFromData consumedCount tag argument
        binderArity data := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let binderArityTerm := shortBinaryNumeralTerm binderArity
  cases data with
  | consumed hconsumed =>
      let certificate := shortNumeralLiteralNeCertificate consumedCount 2
        (‘2’ : ValuationTerm) (termValue_arithmeticTwo termRowsZeroValuation)
        hconsumed
      have hcertificate :=
        shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent
          consumedCount 2 (‘2’ : ValuationTerm)
          (termValue_arithmeticTwo termRowsZeroValuation) hconsumed
      have hselected := transparentHybridDisjunctionLeftPayloadBound_le
        (right := nativeNeFormula tagTerm (‘0’ : ValuationTerm) ⋎
          nativeNeFormula
            (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm)
        certificate _ hcertificate
      simpa only [tripleFailureCertificateFromData,
        tripleFailurePayloadEnvelopeFromData, consumedTerm, tagTerm,
        argumentTerm, binderArityTerm, certificate,
        hybridFormulaStructuralPayloadBound] using hselected
  | tag hconsumed htag =>
      let certificate := shortNumeralLiteralNeCertificate tag 0
        (‘0’ : ValuationTerm) (termValue_arithmeticZero termRowsZeroValuation)
        htag
      have hcertificate :=
        shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent
          tag 0 (‘0’ : ValuationTerm)
          (termValue_arithmeticZero termRowsZeroValuation) htag
      let selected :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := nativeNeFormula
            (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm)
          certificate
      have hselected := transparentHybridDisjunctionLeftPayloadBound_le
        (right := nativeNeFormula
          (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm)
        certificate _ hcertificate
      have houter := transparentHybridDisjunctionRightPayloadBound_le
        (left := nativeNeFormula consumedTerm (‘2’ : ValuationTerm))
        selected _ hselected
      simpa only [tripleFailureCertificateFromData,
        tripleFailurePayloadEnvelopeFromData, consumedTerm, tagTerm,
        argumentTerm, binderArityTerm, certificate, selected,
        hybridFormulaStructuralPayloadBound] using houter
  | argument hconsumed htag hargument =>
      let certificate := nativeNeCertificate
        (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm (by
          simpa [argumentTerm, binderArityTerm, nativeAddTerm,
            termValue_arithmeticAdd, termValue_arithmeticOne,
            termValue_shortBinaryNumeralTerm] using hargument)
      have hcertificate :=
        nativeNeCertificate_structuralPayloadBound_le_transparent
          (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm (by
            simpa [argumentTerm, binderArityTerm, nativeAddTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              termValue_shortBinaryNumeralTerm] using hargument)
      let selected :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := nativeNeFormula tagTerm (‘0’ : ValuationTerm)) certificate
      have hselected := transparentHybridDisjunctionRightPayloadBound_le
        (left := nativeNeFormula tagTerm (‘0’ : ValuationTerm)) certificate _
        hcertificate
      have houter := transparentHybridDisjunctionRightPayloadBound_le
        (left := nativeNeFormula consumedTerm (‘2’ : ValuationTerm))
        selected _ hselected
      simpa only [tripleFailureCertificateFromData,
        tripleFailurePayloadEnvelopeFromData, consumedTerm, tagTerm,
        argumentTerm, binderArityTerm, certificate, selected,
        hybridFormulaStructuralPayloadBound] using houter

def doubleFailurePayloadEnvelopeFromData
    (consumedCount tag : Nat)
    (data : DoubleFailureCheckedData consumedCount tag) : Nat :=
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let consumedFormula := nativeNeFormula consumedTerm (‘2’ : ValuationTerm)
  let tagFormula := nativeNeFormula tagTerm (‘1’ : ValuationTerm)
  match data with
  | .consumed _ =>
      transparentHybridDisjunctionLeftPayloadEnvelope termRowsZeroValuation
        consumedFormula tagFormula
        (termRowsNativeNeStructuralEnvelope consumedTerm
          (‘2’ : ValuationTerm))
  | .tag _ _ =>
      transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
        consumedFormula tagFormula
        (termRowsNativeNeStructuralEnvelope tagTerm (‘1’ : ValuationTerm))

theorem
    doubleFailureCertificateFromData_structuralPayloadBound_le_transparent
    (consumedCount tag : Nat)
    (data : DoubleFailureCheckedData consumedCount tag) :
    hybridFormulaStructuralPayloadBound
        (doubleFailureCertificateFromData consumedCount tag data) <=
      doubleFailurePayloadEnvelopeFromData consumedCount tag data := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  cases data with
  | consumed hconsumed =>
      let certificate := shortNumeralLiteralNeCertificate consumedCount 2
        (‘2’ : ValuationTerm) (termValue_arithmeticTwo termRowsZeroValuation)
        hconsumed
      have hcertificate :=
        shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent
          consumedCount 2 (‘2’ : ValuationTerm)
          (termValue_arithmeticTwo termRowsZeroValuation) hconsumed
      have hselected := transparentHybridDisjunctionLeftPayloadBound_le
        (right := nativeNeFormula tagTerm (‘1’ : ValuationTerm)) certificate _
        hcertificate
      simpa only [doubleFailureCertificateFromData,
        doubleFailurePayloadEnvelopeFromData, consumedTerm, tagTerm,
        certificate, hybridFormulaStructuralPayloadBound] using hselected
  | tag hconsumed htag =>
      let certificate := shortNumeralLiteralNeCertificate tag 1
        (‘1’ : ValuationTerm) (termValue_arithmeticOne termRowsZeroValuation)
        htag
      have hcertificate :=
        shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent
          tag 1 (‘1’ : ValuationTerm)
          (termValue_arithmeticOne termRowsZeroValuation) htag
      have hselected := transparentHybridDisjunctionRightPayloadBound_le
        (left := nativeNeFormula consumedTerm (‘2’ : ValuationTerm))
        certificate _ hcertificate
      simpa only [doubleFailureCertificateFromData,
        doubleFailurePayloadEnvelopeFromData, consumedTerm, tagTerm,
        certificate, hybridFormulaStructuralPayloadBound] using hselected

def otherModesWithTailPayloadEnvelope
    (mode : Nat) (tail : ValuationFormula) (tailResource : Nat) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroFormula := nativeNeFormula modeTerm (‘0’ : ValuationTerm)
  let oneFormula := nativeNeFormula modeTerm (‘1’ : ValuationTerm)
  let twoFormula := nativeNeFormula modeTerm (‘2’ : ValuationTerm)
  let fourFormula := nativeNeFormula modeTerm (‘4’ : ValuationTerm)
  let fiveFormula := nativeNeFormula modeTerm (‘5’ : ValuationTerm)
  let fiveTail := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation fiveFormula tail
    (termRowsNativeNeStructuralEnvelope modeTerm (‘5’ : ValuationTerm))
    tailResource
  let fourTail := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation fourFormula (fiveFormula ⋏ tail)
    (termRowsNativeNeStructuralEnvelope modeTerm (‘4’ : ValuationTerm))
    fiveTail
  let twoTail := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation twoFormula (fourFormula ⋏ (fiveFormula ⋏ tail))
    (termRowsNativeNeStructuralEnvelope modeTerm (‘2’ : ValuationTerm))
    fourTail
  let oneTail := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation oneFormula
    (twoFormula ⋏ (fourFormula ⋏ (fiveFormula ⋏ tail)))
    (termRowsNativeNeStructuralEnvelope modeTerm (‘1’ : ValuationTerm))
    twoTail
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation zeroFormula
    (oneFormula ⋏ (twoFormula ⋏ (fourFormula ⋏ (fiveFormula ⋏ tail))))
    (termRowsNativeNeStructuralEnvelope modeTerm (‘0’ : ValuationTerm))
    oneTail

theorem otherModesWithTailCertificate_structuralPayloadBound_le_transparent
    (mode : Nat)
    (hzero : mode ≠ 0) (hone : mode ≠ 1) (htwo : mode ≠ 2)
    (hfour : mode ≠ 4) (hfive : mode ≠ 5)
    (tail : ValuationFormula)
    (tailCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation tail)
    (tailResource : Nat)
    (htail : hybridFormulaStructuralPayloadBound tailCertificate <=
      tailResource) :
    hybridFormulaStructuralPayloadBound
        (otherModesWithTailCertificate mode hzero hone htwo hfour hfive tail
          tailCertificate) <=
      otherModesWithTailPayloadEnvelope mode tail tailResource := by
  let zeroCertificate := shortNumeralLiteralNeCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation)
    hzero
  let oneCertificate := shortNumeralLiteralNeCertificate mode 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) hone
  let twoCertificate := shortNumeralLiteralNeCertificate mode 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation) htwo
  let fourCertificate := shortNumeralLiteralNeCertificate mode 4
    (‘4’ : ValuationTerm) (termValue_arithmeticFour zeroValuation)
    hfour
  let fiveCertificate := shortNumeralLiteralNeCertificate mode 5
    (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation)
    hfive
  have hzeroResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent mode
      0 (‘0’ : ValuationTerm) (termValue_arithmeticZero termRowsZeroValuation)
      hzero
  have honeResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent mode
      1 (‘1’ : ValuationTerm) (termValue_arithmeticOne termRowsZeroValuation)
      hone
  have htwoResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent mode
      2 (‘2’ : ValuationTerm) (termValue_arithmeticTwo termRowsZeroValuation)
      htwo
  have hfourResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent mode
      4 (‘4’ : ValuationTerm) (termValue_arithmeticFour termRowsZeroValuation)
      hfour
  have hfiveResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent mode
      5 (‘5’ : ValuationTerm) (termValue_arithmeticFive termRowsZeroValuation)
      hfive
  let fiveTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    fiveCertificate tailCertificate
  have hfiveTail := transparentHybridConjunctionPayloadBound_le
    fiveCertificate tailCertificate _ _ hfiveResource htail
  let fourTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    fourCertificate fiveTail
  have hfourTail := transparentHybridConjunctionPayloadBound_le
    fourCertificate fiveTail _ _ hfourResource hfiveTail
  let twoTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    twoCertificate fourTail
  have htwoTail := transparentHybridConjunctionPayloadBound_le
    twoCertificate fourTail _ _ htwoResource hfourTail
  let oneTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    oneCertificate twoTail
  have honeTail := transparentHybridConjunctionPayloadBound_le oneCertificate
    twoTail _ _ honeResource htwoTail
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    zeroCertificate oneTail
  have hdirect := transparentHybridConjunctionPayloadBound_le zeroCertificate
    oneTail _ _ hzeroResource honeTail
  unfold otherModesWithTailCertificate
  change hybridFormulaStructuralPayloadBound direct <= _
  unfold otherModesWithTailPayloadEnvelope
  dsimp only [termRowsZeroValuation, zeroCertificate, oneCertificate,
    twoCertificate, fourCertificate, fiveCertificate, fiveTail, fourTail,
    twoTail, oneTail, direct]
  exact hdirect

noncomputable def compactFormulaTransformTermResidualExistsPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount residual : Nat)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 residual) : Nat :=
  let residualTerm := shortBinaryNumeralTerm residual
  let argumentTerm := shortBinaryNumeralTerm argument
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  let boundFormula := nativeLtFormula residualTerm
    (nativeAddTerm argumentTerm (‘1’ : ValuationTerm))
  let equalityFormula := nativeEqFormula argumentTerm
    (nativeAddTerm witnessCountTerm residualTerm)
  let rowsFormula :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘1’ : ValuationTerm) residualTerm
  let boundResource := termRowsNativeLtStructuralEnvelope residualTerm
    (nativeAddTerm argumentTerm (‘1’ : ValuationTerm))
  let equalityResource := termRowsNativeEqStructuralEnvelope argumentTerm
    (nativeAddTerm witnessCountTerm residualTerm)
  let rowsResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 residual (‘1’ : ValuationTerm) residualTerm hrows
  let equalityRowsResource := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation equalityFormula rowsFormula equalityResource
    rowsResource
  let bodyResource := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation boundFormula (equalityFormula ⋏ rowsFormula)
    boundResource equalityRowsResource
  hybridExistsWitnessStructuralPayloadEnvelope termRowsZeroValuation
    (compactFormulaTransformTermResidualWitnessBody tokenTable width tokenCount
      current next argument witnessCount) residual bodyResource

theorem
    compactFormulaTransformTermResidualExistsCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount residual : Nat)
    (hresidual : residual <= argument)
    (hequality : argument = witnessCount + residual)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 residual) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermResidualExistsCertificate tokenTable width
          tokenCount current next argument witnessCount residual hresidual
          hequality hrows) <=
      compactFormulaTransformTermResidualExistsPayloadEnvelope tokenTable width
        tokenCount current next argument witnessCount residual hrows := by
  let residualTerm := shortBinaryNumeralTerm residual
  let argumentTerm := shortBinaryNumeralTerm argument
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  have hboundValue : termValue termRowsZeroValuation residualTerm <
      termValue termRowsZeroValuation
        (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) := by
    simpa [residualTerm, argumentTerm, nativeAddTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using (Nat.lt_succ_iff.mpr hresidual)
  have hequalityValue : termValue termRowsZeroValuation argumentTerm =
      termValue termRowsZeroValuation
        (nativeAddTerm witnessCountTerm residualTerm) := by
    simpa [argumentTerm, witnessCountTerm, residualTerm, nativeAddTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd] using
      hequality
  let boundCertificate := nativeLtCertificate residualTerm
    (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) hboundValue
  let equalityCertificate := nativeEqCertificate argumentTerm
    (nativeAddTerm witnessCountTerm residualTerm) hequalityValue
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 residual (‘1’ : ValuationTerm) residualTerm
      (termValue_arithmeticOne zeroValuation)
      (by simp [residualTerm, termValue_shortBinaryNumeralTerm]) hrows
  have hboundResource :=
    nativeLtCertificate_structuralPayloadBound_le_transparent residualTerm
      (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) hboundValue
  have hequalityResource :=
    nativeEqCertificate_structuralPayloadBound_le_transparent argumentTerm
      (nativeAddTerm witnessCountTerm residualTerm) hequalityValue
  have hrowsResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 residual (‘1’ : ValuationTerm) residualTerm
      arithmeticOneTerm_freeVariables_eq_empty
      (shortBinaryNumeralTerm_freeVariables_eq_empty residual)
      (termValue_arithmeticOne
        FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation)
      (by simp [residualTerm, termValue_shortBinaryNumeralTerm]) hrows
  let equalityRowsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate rowsCertificate
  have hequalityRows := transparentHybridConjunctionPayloadBound_le
    equalityCertificate rowsCertificate _ _ hequalityResource hrowsResource
  let canonicalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      boundCertificate equalityRowsCertificate
  have hcanonical := transparentHybridConjunctionPayloadBound_le
    boundCertificate equalityRowsCertificate _ _ hboundResource hequalityRows
  let bodyCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      ((compactFormulaTransformTermResidualWitnessBody tokenTable width
        tokenCount current next argument witnessCount)/[residualTerm]) :=
    .cast
      (compactFormulaTransformTermResidualWitnessBody_substitution_alignment
        tokenTable width tokenCount current next argument witnessCount
        residual).symm canonicalCertificate
  have hbody : hybridFormulaStructuralPayloadBound bodyCertificate <=
      transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
        (nativeLtFormula residualTerm
          (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)))
        (nativeEqFormula argumentTerm
            (nativeAddTerm witnessCountTerm residualTerm) ⋏
          FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount (‘1’ : ValuationTerm)
            residualTerm)
        (termRowsNativeLtStructuralEnvelope residualTerm
          (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)))
        (transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
          (nativeEqFormula argumentTerm
            (nativeAddTerm witnessCountTerm residualTerm))
          (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount (‘1’ : ValuationTerm)
            residualTerm)
          (termRowsNativeEqStructuralEnvelope argumentTerm
            (nativeAddTerm witnessCountTerm residualTerm))
          (compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount 1 residual
            (‘1’ : ValuationTerm) residualTerm hrows)) := by
    change hybridFormulaStructuralPayloadBound canonicalCertificate <= _
    dsimp only [termRowsZeroValuation]
    exact hcanonical
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    (compactFormulaTransformTermResidualWitnessBody tokenTable width tokenCount
      current next argument witnessCount) residual bodyCertificate _ hbody
  unfold compactFormulaTransformTermResidualExistsCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        (compactFormulaTransformTermResidualWitnessBody tokenTable width
          tokenCount current next argument witnessCount)
        residual bodyCertificate) <= _
  unfold compactFormulaTransformTermResidualExistsPayloadEnvelope
  dsimp only [residualTerm, argumentTerm, witnessCountTerm,
    boundCertificate, equalityCertificate, rowsCertificate,
    equalityRowsCertificate, canonicalCertificate, bodyCertificate,
    termRowsZeroValuation]
  exact hexists

def termRowsCountFormula
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm current.parserTokensCount)
    (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm next.parserTokensCount))

def termRowsRawPrefixFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat) : ValuationFormula :=
  FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.compactAdditiveNatListAppendSourcePrefixClosedFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount current.start current.parserTokensFinish
    current.parserTokensCount consumedCount next.parserFinish next.finish
    next.outputCount

def termRowsSameFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates) :
    ValuationFormula :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.compactAdditiveNatListSameRowsClosedFormula
    tokenTable width tokenCount current.outputBoundary current.outputCount
    next.outputBoundary next.outputCount

def termRowsGuardZeroTagFormula
    (consumedCount tag argument binderArity : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘2’ : ValuationTerm) ⋏
    (nativeEqFormula (shortBinaryNumeralTerm tag) (‘0’ : ValuationTerm) ⋏
      nativeEqFormula
        (nativeAddTerm (shortBinaryNumeralTerm argument)
          (‘1’ : ValuationTerm))
        (shortBinaryNumeralTerm binderArity))

def termRowsGuardOneTagFormula
    (consumedCount tag : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘2’ : ValuationTerm) ⋏
    nativeEqFormula (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm)

def termRowsAppendTwoOneZeroFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates) :
    ValuationFormula :=
  FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount next.parserFinish next.finish next.outputBoundary
    next.outputCount (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)

def termRowsAppendTwoShiftedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument : Nat) : ValuationFormula :=
  FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount next.parserFinish next.finish next.outputBoundary
    next.outputCount (‘1’ : ValuationTerm)
    (nativeAddTerm (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm))

def termRowsWitnessFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (witnessStart witnessFinish witnessCount : Nat) : ValuationFormula :=
  FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.compactAdditiveNatListAppendSlicesClosedFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount witnessStart witnessFinish witnessCount
    next.parserFinish next.finish next.outputCount

def termRowsOneValueFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument : Nat) : ValuationFormula :=
  FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.compactAdditiveNatListAppendOneValueClosedFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount next.parserFinish next.finish next.outputBoundary
    next.outputCount argument

def termRowsCapturedGuardFormula
    (consumedCount tag argument witnessCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘2’ : ValuationTerm) ⋏
    (nativeEqFormula (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm) ⋏
      nativeLtFormula (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm witnessCount))

def termRowsCapturedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (binderArity argument : Nat) : ValuationFormula :=
  FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount next.parserFinish next.finish next.outputBoundary
    next.outputCount (‘0’ : ValuationTerm)
    (nativeAddTerm (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm argument))

def termRowsResidualGuardFormula
    (consumedCount tag argument witnessCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘2’ : ValuationTerm) ⋏
    (nativeEqFormula (shortBinaryNumeralTerm tag) (‘1’ : ValuationTerm) ⋏
      nativeLeFormula (shortBinaryNumeralTerm witnessCount)
        (shortBinaryNumeralTerm argument))

def termRowsModeZeroFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat) : ValuationFormula :=
  let failure := tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
    (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
    (shortBinaryNumeralTerm binderArity)
  let doubleFailure := doubleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘0’ : ValuationTerm) ⋏
    ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
        termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
          next) ⋎
      ((failure ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
              next argument)) ⋎
        (failure ⋏
          (doubleFailure ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount))))

def termRowsModeOneFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag argument consumedCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘1’ : ValuationTerm) ⋏
    ((termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
          next argument) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount))

def termRowsModeTwoFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘2’ : ValuationTerm) ⋏
    ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
        termRowsWitnessFormula tokenTable width tokenCount current next
          witnessStart witnessFinish witnessCount) ⋎
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount))

def termRowsModeFourFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag argument consumedCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm) ⋏
    ((termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsOneValueFormula tokenTable width tokenCount current next
          argument) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsSameFormula tokenTable width tokenCount current next))

def termRowsModeFiveFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount witnessCount : Nat) :
    ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm) ⋏
    ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) ⋎
      ((termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)))

def termRowsOtherFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode consumedCount : Nat) : ValuationFormula :=
  otherModesWithTailFormula (shortBinaryNumeralTerm mode)
    (termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount)

def termRowsModesFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : ValuationFormula :=
  termRowsModeZeroFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount ⋎
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount))))

def termRowsZeroCaseFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘0’ : ValuationTerm) ⋏
    termRowsSameFormula tokenTable width tokenCount current next

def termRowsPositiveCaseFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : ValuationFormula :=
  nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount) ⋏
    termRowsModesFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount

def termRowsCasesFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : ValuationFormula :=
  termRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount ⋎
    termRowsPositiveCaseFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount

theorem compactFormulaTransformTermOutputRowsExplicitFormula_eq_named :
    compactFormulaTransformTermOutputRowsExplicitFormula =
      fun tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount =>
        termRowsCountFormula current next consumedCount ⋏
          termRowsCasesFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessStart witnessFinish
            witnessCount := by
  funext tokenTable width tokenCount current next mode binderArity tag argument
    consumedCount witnessStart witnessFinish witnessCount
  rfl

def termRowsModeOuterPayloadEnvelope
    (modeTerm literal : ValuationTerm)
    (body : ValuationFormula) (bodyResource : Nat) : Nat :=
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    (nativeEqFormula modeTerm literal) body
    (termRowsNativeEqStructuralEnvelope modeTerm literal) bodyResource

theorem termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
    (modeTerm literal : ValuationTerm)
    (modeCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation (nativeEqFormula modeTerm literal))
    (body : ValuationFormula)
    (bodyCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation body)
    (bodyResource : Nat)
    (hmode : hybridFormulaStructuralPayloadBound modeCertificate <=
      termRowsNativeEqStructuralEnvelope modeTerm literal)
    (hbody : hybridFormulaStructuralPayloadBound bodyCertificate <=
      bodyResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          modeCertificate bodyCertificate) <=
      termRowsModeOuterPayloadEnvelope modeTerm literal body bodyResource := by
  simpa only [termRowsModeOuterPayloadEnvelope] using
    transparentHybridConjunctionPayloadBound_le modeCertificate bodyCertificate
      _ _ hmode hbody

def termRowsModeZeroPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount selectedResource : Nat) : Nat :=
  transparentHybridDisjunctionLeftPayloadEnvelope termRowsZeroValuation
    (termRowsModeZeroFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount)
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount)))) selectedResource

def termRowsModeOnePathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount selectedResource : Nat) : Nat :=
  let selected := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount ⋎
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount))) selectedResource
  transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
    (termRowsModeZeroFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount)
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount)))) selected

def termRowsModeTwoPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount selectedResource : Nat) : Nat :=
  let selected := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount)
    (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeFiveFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount)) selectedResource
  let middle := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount ⋎
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount))) selected
  transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
    (termRowsModeZeroFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount)
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount)))) middle

def termRowsModeFourPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount selectedResource : Nat) : Nat :=
  let selected := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeFiveFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessCount ⋎
      termRowsOtherFormula tokenTable width tokenCount current next mode
        consumedCount) selectedResource
  let afterTwo := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount)
    (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeFiveFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount)) selected
  let afterOne := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount ⋎
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount))) afterTwo
  transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
    (termRowsModeZeroFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount)
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount)))) afterOne

def termRowsModeFivePathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount selectedResource : Nat) : Nat :=
  let selected := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeFiveFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessCount)
    (termRowsOtherFormula tokenTable width tokenCount current next mode
      consumedCount) selectedResource
  let afterFour := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeFiveFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessCount ⋎
      termRowsOtherFormula tokenTable width tokenCount current next mode
        consumedCount) selected
  let afterTwo := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount)
    (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeFiveFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount)) afterFour
  let afterOne := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount ⋎
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount))) afterTwo
  transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
    (termRowsModeZeroFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount)
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount)))) afterOne

def termRowsOtherPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount selectedResource : Nat) : Nat :=
  let afterFive := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeFiveFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessCount)
    (termRowsOtherFormula tokenTable width tokenCount current next mode
      consumedCount) selectedResource
  let afterFour := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeFiveFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessCount ⋎
      termRowsOtherFormula tokenTable width tokenCount current next mode
        consumedCount) afterFive
  let afterTwo := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount)
    (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeFiveFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount)) afterFour
  let afterOne := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
      argument consumedCount)
    (termRowsModeTwoFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount ⋎
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount))) afterTwo
  transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
    (termRowsModeZeroFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount)
    (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount)))) afterOne

def termRowsPositiveSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount modesResource : Nat) : Nat :=
  let positiveResource := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount))
    (termRowsModesFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount)
    (termRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)) modesResource
  let casesResource := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount)
    (termRowsPositiveCaseFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) positiveResource
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    (termRowsCountFormula current next consumedCount)
    (termRowsCasesFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount)
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount))) casesResource

def termRowsZeroSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount sameResource : Nat) : Nat :=
  let zeroResource := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘0’ : ValuationTerm))
    (termRowsSameFormula tokenTable width tokenCount current next)
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm))
    sameResource
  let casesResource := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount)
    (termRowsPositiveCaseFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) zeroResource
  transparentHybridConjunctionPayloadEnvelope termRowsZeroValuation
    (termRowsCountFormula current next consumedCount)
    (termRowsCasesFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount)
    (termRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount))) casesResource

theorem termRowsModeZeroPathCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (certificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsModeZeroFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount))
    (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := termRowsModeOneFormula tokenTable width tokenCount current
              next mode tag argument consumedCount ⋎
            (termRowsModeTwoFormula tokenTable width tokenCount current next
                mode binderArity tag argument consumedCount witnessStart
                witnessFinish witnessCount ⋎
              (termRowsModeFourFormula tokenTable width tokenCount current next
                  mode tag argument consumedCount ⋎
                (termRowsModeFiveFormula tokenTable width tokenCount current
                    next mode binderArity tag argument consumedCount
                    witnessCount ⋎
                  termRowsOtherFormula tokenTable width tokenCount current next
                    mode consumedCount)))) certificate) <=
      termRowsModeZeroPathPayloadEnvelope tokenTable width tokenCount current
        next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount resource := by
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount ⋎
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount)))) certificate resource hcertificate
  simpa only [termRowsModeZeroPathPayloadEnvelope] using hselected

theorem termRowsModeOnePathCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (certificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
        argument consumedCount))
    (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsModeZeroFormula tokenTable width tokenCount current
            next mode binderArity tag argument consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := termRowsModeTwoFormula tokenTable width tokenCount current
                next mode binderArity tag argument consumedCount witnessStart
                witnessFinish witnessCount ⋎
              (termRowsModeFourFormula tokenTable width tokenCount current next
                  mode tag argument consumedCount ⋎
                (termRowsModeFiveFormula tokenTable width tokenCount current
                    next mode binderArity tag argument consumedCount
                    witnessCount ⋎
                  termRowsOtherFormula tokenTable width tokenCount current next
                    mode consumedCount))) certificate)) <=
      termRowsModeOnePathPayloadEnvelope tokenTable width tokenCount current
        next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount resource := by
  let selected := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount ⋎
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount))) certificate
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount ⋎
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount))) certificate resource hcertificate
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeZeroFormula tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount) selected _ hselected
  simpa only [termRowsModeOnePathPayloadEnvelope, selected] using houter

theorem termRowsModeTwoPathCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (certificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsModeTwoFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount))
    (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsModeZeroFormula tokenTable width tokenCount current
            next mode binderArity tag argument consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := termRowsModeOneFormula tokenTable width tokenCount current
              next mode tag argument consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := termRowsModeFourFormula tokenTable width tokenCount
                  current next mode tag argument consumedCount ⋎
                (termRowsModeFiveFormula tokenTable width tokenCount current
                    next mode binderArity tag argument consumedCount
                    witnessCount ⋎
                  termRowsOtherFormula tokenTable width tokenCount current next
                    mode consumedCount)) certificate))) <=
      termRowsModeTwoPathPayloadEnvelope tokenTable width tokenCount current
        next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount resource := by
  let selected := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := termRowsModeFourFormula tokenTable width tokenCount current next
        mode tag argument consumedCount ⋎
      (termRowsModeFiveFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount)) certificate
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termRowsModeFourFormula tokenTable width tokenCount current next
        mode tag argument consumedCount ⋎
      (termRowsModeFiveFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount)) certificate resource hcertificate
  let middle := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeOneFormula tokenTable width tokenCount current next
      mode tag argument consumedCount) selected
  have hmiddle := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeOneFormula tokenTable width tokenCount current next
      mode tag argument consumedCount) selected _ hselected
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeZeroFormula tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount) middle _ hmiddle
  simpa only [termRowsModeTwoPathPayloadEnvelope, selected, middle] using houter

theorem termRowsModeFourPathCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (certificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsModeFourFormula tokenTable width tokenCount current next mode tag
        argument consumedCount))
    (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsModeZeroFormula tokenTable width tokenCount current
            next mode binderArity tag argument consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := termRowsModeOneFormula tokenTable width tokenCount current
              next mode tag argument consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := termRowsModeTwoFormula tokenTable width tokenCount
                current next mode binderArity tag argument consumedCount
                witnessStart witnessFinish witnessCount)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := termRowsModeFiveFormula tokenTable width tokenCount
                    current next mode binderArity tag argument consumedCount
                    witnessCount ⋎
                  termRowsOtherFormula tokenTable width tokenCount current next
                    mode consumedCount) certificate)))) <=
      termRowsModeFourPathPayloadEnvelope tokenTable width tokenCount current
        next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount resource := by
  let selected := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := termRowsModeFiveFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessCount ⋎
      termRowsOtherFormula tokenTable width tokenCount current next mode
        consumedCount) certificate
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termRowsModeFiveFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessCount ⋎
      termRowsOtherFormula tokenTable width tokenCount current next mode
        consumedCount) certificate resource hcertificate
  let afterTwo := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) selected
  have hafterTwo := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) selected _ hselected
  let afterOne := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeOneFormula tokenTable width tokenCount current next mode
      tag argument consumedCount) afterTwo
  have hafterOne := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeOneFormula tokenTable width tokenCount current next mode
      tag argument consumedCount) afterTwo _ hafterTwo
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeZeroFormula tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount) afterOne _ hafterOne
  simpa only [termRowsModeFourPathPayloadEnvelope, selected, afterTwo,
    afterOne] using houter

theorem termRowsModeFivePathCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (certificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsModeFiveFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessCount))
    (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsModeZeroFormula tokenTable width tokenCount current
            next mode binderArity tag argument consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := termRowsModeOneFormula tokenTable width tokenCount current
              next mode tag argument consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := termRowsModeTwoFormula tokenTable width tokenCount
                current next mode binderArity tag argument consumedCount
                witnessStart witnessFinish witnessCount)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := termRowsModeFourFormula tokenTable width tokenCount
                  current next mode tag argument consumedCount)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (right := termRowsOtherFormula tokenTable width tokenCount
                    current next mode consumedCount) certificate))))) <=
      termRowsModeFivePathPayloadEnvelope tokenTable width tokenCount current
        next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount resource := by
  let selected := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := termRowsOtherFormula tokenTable width tokenCount current next mode
      consumedCount) certificate
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termRowsOtherFormula tokenTable width tokenCount current next mode
      consumedCount) certificate resource hcertificate
  let afterFour := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeFourFormula tokenTable width tokenCount current next
      mode tag argument consumedCount) selected
  have hafterFour := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeFourFormula tokenTable width tokenCount current next
      mode tag argument consumedCount) selected _ hselected
  let afterTwo := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) afterFour
  have hafterTwo := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) afterFour _ hafterFour
  let afterOne := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeOneFormula tokenTable width tokenCount current next mode
      tag argument consumedCount) afterTwo
  have hafterOne := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeOneFormula tokenTable width tokenCount current next mode
      tag argument consumedCount) afterTwo _ hafterTwo
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeZeroFormula tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount) afterOne _ hafterOne
  simpa only [termRowsModeFivePathPayloadEnvelope, selected, afterFour,
    afterTwo, afterOne] using houter

theorem termRowsOtherPathCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (certificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsOtherFormula tokenTable width tokenCount current next mode
        consumedCount))
    (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsModeZeroFormula tokenTable width tokenCount current
            next mode binderArity tag argument consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := termRowsModeOneFormula tokenTable width tokenCount current
              next mode tag argument consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := termRowsModeTwoFormula tokenTable width tokenCount
                current next mode binderArity tag argument consumedCount
                witnessStart witnessFinish witnessCount)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := termRowsModeFourFormula tokenTable width tokenCount
                  current next mode tag argument consumedCount)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left := termRowsModeFiveFormula tokenTable width tokenCount
                    current next mode binderArity tag argument consumedCount
                    witnessCount) certificate))))) <=
      termRowsOtherPathPayloadEnvelope tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount resource := by
  let afterFive := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeFiveFormula tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount witnessCount) certificate
  have hafterFive := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeFiveFormula tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount witnessCount) certificate _
    hcertificate
  let afterFour := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeFourFormula tokenTable width tokenCount current next
      mode tag argument consumedCount) afterFive
  have hafterFour := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeFourFormula tokenTable width tokenCount current next
      mode tag argument consumedCount) afterFive _ hafterFive
  let afterTwo := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) afterFour
  have hafterTwo := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeTwoFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount) afterFour _ hafterFour
  let afterOne := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsModeOneFormula tokenTable width tokenCount current next mode
      tag argument consumedCount) afterTwo
  have hafterOne := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeOneFormula tokenTable width tokenCount current next mode
      tag argument consumedCount) afterTwo _ hafterTwo
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsModeZeroFormula tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount) afterOne _ hafterOne
  simpa only [termRowsOtherPathPayloadEnvelope, afterFive, afterFour, afterTwo,
    afterOne] using houter

theorem termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (countCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation (termRowsCountFormula current next consumedCount))
    (positiveCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount)))
    (modesCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsModesFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount))
    (modesResource : Nat)
    (hcount : hybridFormulaStructuralPayloadBound countCertificate <=
      termRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)))
    (hpositive : hybridFormulaStructuralPayloadBound positiveCertificate <=
      termRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount))
    (hmodes : hybridFormulaStructuralPayloadBound modesCertificate <=
      modesResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          countCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := termRowsZeroCaseFormula tokenTable width tokenCount current
              next consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              positiveCertificate modesCertificate))) <=
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource := by
  let positive := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    positiveCertificate modesCertificate
  have hpositiveSelected := transparentHybridConjunctionPayloadBound_le
    positiveCertificate modesCertificate _ _ hpositive hmodes
  let cases := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive
  have hcases := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive _ hpositiveSelected
  have houter := transparentHybridConjunctionPayloadBound_le countCertificate
    cases _ _ hcount hcases
  simpa only [termRowsPositiveSelectedPayloadEnvelope,
    termRowsCasesFormula, termRowsPositiveCaseFormula, positive, cases] using
    houter

theorem termRowsZeroSelectedCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (countCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation (termRowsCountFormula current next consumedCount))
    (zeroCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
        (‘0’ : ValuationTerm)))
    (sameCertificate : CheckedHybridValuationBoundedFormulaCertificate
      termRowsZeroValuation
      (termRowsSameFormula tokenTable width tokenCount current next))
    (sameResource : Nat)
    (hcount : hybridFormulaStructuralPayloadBound countCertificate <=
      termRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)))
    (hzero : hybridFormulaStructuralPayloadBound zeroCertificate <=
      termRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm))
    (hsame : hybridFormulaStructuralPayloadBound sameCertificate <=
      sameResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          countCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := termRowsPositiveCaseFormula tokenTable width tokenCount
              current next mode binderArity tag argument consumedCount
              witnessStart witnessFinish witnessCount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              zeroCertificate sameCertificate))) <=
      termRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount sameResource := by
  let zero := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    zeroCertificate sameCertificate
  have hzeroSelected := transparentHybridConjunctionPayloadBound_le
    zeroCertificate sameCertificate _ _ hzero hsame
  let cases := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := termRowsPositiveCaseFormula tokenTable width tokenCount current
      next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) zero
  have hcases := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termRowsPositiveCaseFormula tokenTable width tokenCount current
      next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) zero _ hzeroSelected
  have houter := transparentHybridConjunctionPayloadBound_le countCertificate
    cases _ _ hcount hcases
  simpa only [termRowsZeroSelectedPayloadEnvelope, termRowsCasesFormula,
    termRowsZeroCaseFormula, zero, cases] using houter

noncomputable def
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (data : CompactFormulaTransformTermOutputRowsCheckedBranchData tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  match data with
  | .zero _ _ hsame =>
      termRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hsame)
  | .modeZeroLower _ _ _ _ hrows =>
      let guardRows := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardZeroTagFormula consumedCount tag argument binderArity)
        (termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
          next)
        (zeroTagGuardPayloadEnvelope consumedCount tag argument binderArity)
        (compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 0 (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
          hrows)
      let internal := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
            next)
        ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (termRowsGuardOneTagFormula consumedCount tag ⋏
              termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                current next argument)) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount))) guardRows
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘0’ : ValuationTerm)
        ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
            termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
              next) ⋎
          ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
                (shortBinaryNumeralTerm binderArity) ⋏
              (termRowsGuardOneTagFormula consumedCount tag ⋏
                termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                  current next argument)) ⋎
            (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
                (shortBinaryNumeralTerm binderArity) ⋏
              (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                  (shortBinaryNumeralTerm tag) ⋏
                termRowsRawPrefixFormula tokenTable width tokenCount current
                  next consumedCount)))) internal
      let modesResource := termRowsModeZeroPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeZeroShifted _ _ _ failure _ hrows =>
      let guardRows := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation (termRowsGuardOneTagFormula consumedCount tag)
        (termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
          next argument)
        (oneTagGuardPayloadEnvelope consumedCount tag)
        (compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm argument)
            (‘1’ : ValuationTerm)) hrows)
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity))
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
            next argument)
        (tripleFailurePayloadEnvelopeFromData consumedCount tag argument
          binderArity failure) guardRows
      let middle := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
              next argument))
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) selected
      let internal := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
            next)
        ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (termRowsGuardOneTagFormula consumedCount tag ⋏
              termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                current next argument)) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount))) middle
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘0’ : ValuationTerm)
        ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
            termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
              next) ⋎
          ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
                (shortBinaryNumeralTerm binderArity) ⋏
              (termRowsGuardOneTagFormula consumedCount tag ⋏
                termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                  current next argument)) ⋎
            (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
                (shortBinaryNumeralTerm binderArity) ⋏
              (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                  (shortBinaryNumeralTerm tag) ⋏
                termRowsRawPrefixFormula tokenTable width tokenCount current
                  next consumedCount)))) internal
      let modesResource := termRowsModeZeroPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeZeroRaw _ _ _ lowerFailure shiftFailure hrows =>
      let shiftRows := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag))
        (termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)
        (doubleFailurePayloadEnvelopeFromData consumedCount tag shiftFailure)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows)
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity))
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)
        (tripleFailurePayloadEnvelopeFromData consumedCount tag argument
          binderArity lowerFailure) shiftRows
      let middle := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
              next argument))
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) selected
      let internal := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
            next)
        ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (termRowsGuardOneTagFormula consumedCount tag ⋏
              termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                current next argument)) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount))) middle
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘0’ : ValuationTerm)
        ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
            termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
              next) ⋎
          ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
                (shortBinaryNumeralTerm binderArity) ⋏
              (termRowsGuardOneTagFormula consumedCount tag ⋏
                termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                  current next argument)) ⋎
            (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
                (shortBinaryNumeralTerm binderArity) ⋏
              (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                  (shortBinaryNumeralTerm tag) ⋏
                termRowsRawPrefixFormula tokenTable width tokenCount current
                  next consumedCount)))) internal
      let modesResource := termRowsModeZeroPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeOneShifted _ _ _ _ hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation (termRowsGuardOneTagFormula consumedCount tag)
        (termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
          next argument)
        (oneTagGuardPayloadEnvelope consumedCount tag)
        (compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm argument)
            (‘1’ : ValuationTerm)) hrows)
      let internal := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
            next argument)
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount) selected
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘1’ : ValuationTerm)
        ((termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
              next argument) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) internal
      let modesResource := termRowsModeOnePathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeOneRaw _ _ _ failure hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag))
        (termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)
        (doubleFailurePayloadEnvelopeFromData consumedCount tag failure)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows)
      let internal := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
            next argument)
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount) selected
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘1’ : ValuationTerm)
        ((termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
              next argument) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) internal
      let modesResource := termRowsModeOnePathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeTwoLower _ _ _ _ hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardZeroTagFormula consumedCount tag argument binderArity)
        (termRowsWitnessFormula tokenTable width tokenCount current next
          witnessStart witnessFinish witnessCount)
        (zeroTagGuardPayloadEnvelope consumedCount tag argument binderArity)
        (compactAdditiveNatListAppendSlicesGraphPayloadEnvelope tokenTable width
          tokenCount current.parserFinish current.finish current.outputCount
          witnessStart witnessFinish witnessCount next.parserFinish next.finish
          next.outputCount hrows)
      let internal := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsWitnessFormula tokenTable width tokenCount current next
            witnessStart witnessFinish witnessCount)
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount) selected
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘2’ : ValuationTerm)
        ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
            termRowsWitnessFormula tokenTable width tokenCount current next
              witnessStart witnessFinish witnessCount) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) internal
      let modesResource := termRowsModeTwoPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeTwoRaw _ _ _ failure hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity))
        (termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)
        (tripleFailurePayloadEnvelopeFromData consumedCount tag argument
          binderArity failure)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows)
      let internal := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsWitnessFormula tokenTable width tokenCount current next
            witnessStart witnessFinish witnessCount)
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount) selected
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘2’ : ValuationTerm)
        ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
            termRowsWitnessFormula tokenTable width tokenCount current next
              witnessStart witnessFinish witnessCount) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) internal
      let modesResource := termRowsModeTwoPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeFourOne _ _ _ _ hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation (termRowsGuardOneTagFormula consumedCount tag)
        (termRowsOneValueFormula tokenTable width tokenCount current next
          argument)
        (oneTagGuardPayloadEnvelope consumedCount tag)
        (compactAdditiveNatListAppendOneValueGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount argument hrows)
      let internal := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsOneValueFormula tokenTable width tokenCount current next
            argument)
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsSameFormula tokenTable width tokenCount current next) selected
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘4’ : ValuationTerm)
        ((termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsOneValueFormula tokenTable width tokenCount current next
              argument) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsSameFormula tokenTable width tokenCount current next))
        internal
      let modesResource := termRowsModeFourPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeFourSame _ _ _ failure hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag))
        (termRowsSameFormula tokenTable width tokenCount current next)
        (doubleFailurePayloadEnvelopeFromData consumedCount tag failure)
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows)
      let internal := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsOneValueFormula tokenTable width tokenCount current next
            argument)
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsSameFormula tokenTable width tokenCount current next) selected
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘4’ : ValuationTerm)
        ((termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsOneValueFormula tokenTable width tokenCount current next
              argument) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsSameFormula tokenTable width tokenCount current next))
        internal
      let modesResource := termRowsModeFourPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeFiveCaptured _ _ _ _ hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (termRowsCapturedGuardFormula consumedCount tag argument witnessCount)
        (termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument)
        (capturedGuardPayloadEnvelope consumedCount tag argument witnessCount)
        (compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm argument)) hrows)
      let internal := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation
        (termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
          termRowsCapturedFormula tokenTable width tokenCount current next
            binderArity argument)
        ((termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
            compactFormulaTransformTermResidualExistsFormula tokenTable width
              tokenCount current next argument witnessCount) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) selected
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘5’ : ValuationTerm)
        ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
            termRowsCapturedFormula tokenTable width tokenCount current next
              binderArity argument) ⋎
          ((termRowsResidualGuardFormula consumedCount tag argument
                witnessCount ⋏
              compactFormulaTransformTermResidualExistsFormula tokenTable width
                tokenCount current next argument witnessCount) ⋎
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount))) internal
      let modesResource := termRowsModeFivePathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeFiveResidual _ _ _ _ residual _ _ hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (termRowsResidualGuardFormula consumedCount tag argument witnessCount)
        (compactFormulaTransformTermResidualExistsFormula tokenTable width
          tokenCount current next argument witnessCount)
        (residualGuardPayloadEnvelope consumedCount tag argument witnessCount)
        (compactFormulaTransformTermResidualExistsPayloadEnvelope tokenTable
          width tokenCount current next argument witnessCount residual hrows)
      let middle := transparentHybridDisjunctionLeftPayloadEnvelope
        termRowsZeroValuation
        (termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount)
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount) selected
      let internal := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
          termRowsCapturedFormula tokenTable width tokenCount current next
            binderArity argument)
        ((termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
            compactFormulaTransformTermResidualExistsFormula tokenTable width
              tokenCount current next argument witnessCount) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) middle
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘5’ : ValuationTerm)
        ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
            termRowsCapturedFormula tokenTable width tokenCount current next
              binderArity argument) ⋎
          ((termRowsResidualGuardFormula consumedCount tag argument
                witnessCount ⋏
              compactFormulaTransformTermResidualExistsFormula tokenTable width
                tokenCount current next argument witnessCount) ⋎
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount))) internal
      let modesResource := termRowsModeFivePathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .modeFiveRaw _ _ _ failure hrows =>
      let selected := transparentHybridConjunctionPayloadEnvelope
        termRowsZeroValuation
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag))
        (termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)
        (doubleFailurePayloadEnvelopeFromData consumedCount tag failure)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows)
      let middle := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount)
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount) selected
      let internal := transparentHybridDisjunctionRightPayloadEnvelope
        termRowsZeroValuation
        (termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
          termRowsCapturedFormula tokenTable width tokenCount current next
            binderArity argument)
        ((termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
            compactFormulaTransformTermResidualExistsFormula tokenTable width
              tokenCount current next argument witnessCount) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount)) middle
      let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
        (‘5’ : ValuationTerm)
        ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
            termRowsCapturedFormula tokenTable width tokenCount current next
              binderArity argument) ⋎
          ((termRowsResidualGuardFormula consumedCount tag argument
                witnessCount ⋏
              compactFormulaTransformTermResidualExistsFormula tokenTable width
                tokenCount current next argument witnessCount) ⋎
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount))) internal
      let modesResource := termRowsModeFivePathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount modeResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource
  | .other _ _ _ _ _ _ _ hrows =>
      let rawResource :=
        compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows
      let otherResource := otherModesWithTailPayloadEnvelope mode
        (termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount) rawResource
      let modesResource := termRowsOtherPathPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount otherResource
      termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount modesResource

theorem
    compactFormulaTransformTermOutputRowsZeroBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : consumedCount = 0)
    (hsame : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.zero hcount hconsumed hsame)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.zero hcount hconsumed hsame) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let zeroCertificate := consumedCountZeroCertificate consumedCount hconsumed
  let sameCertificate :=
    FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hzeroResource :=
    consumedCountZeroCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hsameResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  have htop := termRowsZeroSelectedCertificate_structuralPayloadBound_le_transparent
    tokenTable width tokenCount current next mode binderArity tag argument
    consumedCount witnessStart witnessFinish witnessCount countCertificate
    zeroCertificate sameCertificate
    (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
      tokenCount current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount hsame) hcountResource hzeroResource hsameResource
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := termRowsPositiveCaseFormula tokenTable width tokenCount
            current next mode binderArity tag argument consumedCount
            witnessStart witnessFinish witnessCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            zeroCertificate sameCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeZeroLowerBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 0) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeZeroLower hcount hconsumed hmode hguard hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeZeroLower hcount hconsumed hmode hguard hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
  let guardCertificate := zeroTagGuardCertificate consumedCount tag argument
    binderArity hguard
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 0 (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
      (termValue_arithmeticOne zeroValuation)
      (termValue_arithmeticZero zeroValuation) hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 0 (‘0’ : ValuationTerm)
      (termValue_arithmeticZero termRowsZeroValuation) hmode
  have hguardResource :=
    zeroTagGuardCertificate_structuralPayloadBound_le_transparent consumedCount
      tag argument binderArity hguard
  have hrowsResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 0 (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
      arithmeticOneTerm_freeVariables_eq_empty
      arithmeticZeroTerm_freeVariables_eq_empty
      (termValue_arithmeticOne
        FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation)
      (termValue_arithmeticZero
        FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation)
      hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    guardCertificate rowsCertificate _ _ hguardResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
              next argument)) ⋎
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount))) selected
  have hinternal := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
              next argument)) ⋎
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount))) selected _ hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘0’ : ValuationTerm) modeCertificate
      ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
            next) ⋎
        ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (termRowsGuardOneTagFormula consumedCount tag ⋏
              termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                current next argument)) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount)))) internal _ hmodeResource hinternal
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeOneFormula tokenTable width tokenCount current next
          mode tag argument consumedCount ⋎
        (termRowsModeTwoFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessStart witnessFinish
            witnessCount ⋎
          (termRowsModeFourFormula tokenTable width tokenCount current next mode
              tag argument consumedCount ⋎
            (termRowsModeFiveFormula tokenTable width tokenCount current next
                mode binderArity tag argument consumedCount witnessCount ⋎
              termRowsOtherFormula tokenTable width tokenCount current next mode
                consumedCount)))) modeFull
  have hmodes :=
    termRowsModeZeroPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeZeroShiftedBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 (argument + 1)) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeZeroShifted hcount hconsumed hmode failure hguard hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeZeroShifted hcount hconsumed hmode failure hguard hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
  let failureCertificate := tripleFailureCertificateFromData consumedCount tag
    argument binderArity failure
  let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
  let shiftedTerm := nativeAddTerm (shortBinaryNumeralTerm argument)
    (‘1’ : ValuationTerm)
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm) shiftedTerm
      (termValue_arithmeticOne zeroValuation)
      (by
        simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 0 (‘0’ : ValuationTerm)
      (termValue_arithmeticZero termRowsZeroValuation) hmode
  have hfailureResource :=
    tripleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag argument binderArity failure
  have hguardResource :=
    oneTagGuardCertificate_structuralPayloadBound_le_transparent consumedCount
      tag hguard
  have hshiftedClosed : shiftedTerm.freeVariables = ∅ := by
    exact nativeAddTerm_freeVariables_eq_empty _ _
      (shortBinaryNumeralTerm_freeVariables_eq_empty argument)
      arithmeticOneTerm_freeVariables_eq_empty
  have hrowsResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm) shiftedTerm
      arithmeticOneTerm_freeVariables_eq_empty hshiftedClosed
      (termValue_arithmeticOne
        FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation)
      (by
        simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
  let guardRows := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate rowsCertificate
  have hguardRows := transparentHybridConjunctionPayloadBound_le
    guardCertificate rowsCertificate _ _ hguardResource hrowsResource
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    failureCertificate guardRows
  have hselected := transparentHybridConjunctionPayloadBound_le
    failureCertificate guardRows _ _ hfailureResource hguardRows
  let middle := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) selected
  have hmiddle := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) selected _ hselected
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsGuardZeroTagFormula consumedCount tag argument
        binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current next)
    middle
  have hinternal := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsGuardZeroTagFormula consumedCount tag argument
        binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current next)
    middle _ hmiddle
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘0’ : ValuationTerm) modeCertificate
      ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
            next) ⋎
        ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (termRowsGuardOneTagFormula consumedCount tag ⋏
              termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                current next argument)) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount)))) internal _ hmodeResource hinternal
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeOneFormula tokenTable width tokenCount current next
          mode tag argument consumedCount ⋎
        (termRowsModeTwoFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessStart witnessFinish
            witnessCount ⋎
          (termRowsModeFourFormula tokenTable width tokenCount current next mode
              tag argument consumedCount ⋎
            (termRowsModeFiveFormula tokenTable width tokenCount current next
                mode binderArity tag argument consumedCount witnessCount ⋎
              termRowsOtherFormula tokenTable width tokenCount current next mode
                consumedCount)))) modeFull
  have hmodes :=
    termRowsModeZeroPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only [shiftedTerm]
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeZeroRawBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (lowerFailure : TripleFailureCheckedData
      consumedCount tag argument binderArity)
    (shiftFailure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure
            hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
  let lowerFailureCertificate := tripleFailureCertificateFromData consumedCount
    tag argument binderArity lowerFailure
  let shiftFailureCertificate := doubleFailureCertificateFromData consumedCount
    tag shiftFailure
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 0 (‘0’ : ValuationTerm)
      (termValue_arithmeticZero termRowsZeroValuation) hmode
  have hlowerFailureResource :=
    tripleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag argument binderArity lowerFailure
  have hshiftFailureResource :=
    doubleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag shiftFailure
  have hrowsResource :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let shiftRows := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    shiftFailureCertificate rowsCertificate
  have hshiftRows := transparentHybridConjunctionPayloadBound_le
    shiftFailureCertificate rowsCertificate _ _ hshiftFailureResource
    hrowsResource
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    lowerFailureCertificate shiftRows
  have hselected := transparentHybridConjunctionPayloadBound_le
    lowerFailureCertificate shiftRows _ _ hlowerFailureResource hshiftRows
  let middle := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left :=
      tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
            next argument)) selected
  have hmiddle := transparentHybridDisjunctionRightPayloadBound_le
    (left :=
      tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
            next argument)) selected _ hselected
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsGuardZeroTagFormula consumedCount tag argument
        binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current next)
    middle
  have hinternal := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsGuardZeroTagFormula consumedCount tag argument
        binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current next)
    middle _ hmiddle
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘0’ : ValuationTerm) modeCertificate
      ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
            next) ⋎
        ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (termRowsGuardOneTagFormula consumedCount tag ⋏
              termRowsAppendTwoShiftedFormula tokenTable width tokenCount
                current next argument)) ⋎
          (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
              (shortBinaryNumeralTerm binderArity) ⋏
            (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
                (shortBinaryNumeralTerm tag) ⋏
              termRowsRawPrefixFormula tokenTable width tokenCount current next
                consumedCount)))) internal _ hmodeResource hinternal
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeOneFormula tokenTable width tokenCount current next
          mode tag argument consumedCount ⋎
        (termRowsModeTwoFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessStart witnessFinish
            witnessCount ⋎
          (termRowsModeFourFormula tokenTable width tokenCount current next mode
              tag argument consumedCount ⋎
            (termRowsModeFiveFormula tokenTable width tokenCount current next
                mode binderArity tag argument consumedCount witnessCount ⋎
              termRowsOtherFormula tokenTable width tokenCount current next mode
                consumedCount)))) modeFull
  have hmodes :=
    termRowsModeZeroPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeOneShiftedBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 1)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 (argument + 1)) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeOneShifted hcount hconsumed hmode hguard hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeOneShifted hcount hconsumed hmode hguard hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) hmode
  let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
  let shiftedTerm := nativeAddTerm (shortBinaryNumeralTerm argument)
    (‘1’ : ValuationTerm)
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm) shiftedTerm
      (termValue_arithmeticOne zeroValuation)
      (by
        simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 1 (‘1’ : ValuationTerm)
      (termValue_arithmeticOne termRowsZeroValuation) hmode
  have hguardResource :=
    oneTagGuardCertificate_structuralPayloadBound_le_transparent consumedCount
      tag hguard
  have hshiftedClosed : shiftedTerm.freeVariables = ∅ :=
    nativeAddTerm_freeVariables_eq_empty _ _
      (shortBinaryNumeralTerm_freeVariables_eq_empty argument)
      arithmeticOneTerm_freeVariables_eq_empty
  have hrowsResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm) shiftedTerm
      arithmeticOneTerm_freeVariables_eq_empty hshiftedClosed
      (termValue_arithmeticOne
        FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation)
      (by
        simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    guardCertificate rowsCertificate _ _ hguardResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount) selected
  have hinternal := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount) selected _ hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘1’ : ValuationTerm) modeCertificate
      ((termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
            next argument) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeTwoFormula tokenTable width tokenCount current next
          mode binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount))) modeFull
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) selectedPath
  have hmodes :=
    termRowsModeOnePathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only [shiftedTerm]
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeOneRawBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 1)
    (failure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeOneRaw hcount hconsumed hmode failure hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeOneRaw hcount hconsumed hmode failure hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) hmode
  let failureCertificate := doubleFailureCertificateFromData consumedCount tag
    failure
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 1 (‘1’ : ValuationTerm)
      (termValue_arithmeticOne termRowsZeroValuation) hmode
  have hfailureResource :=
    doubleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag failure
  have hrowsResource :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    failureCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    failureCertificate rowsCertificate _ _ hfailureResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsAppendTwoShiftedFormula tokenTable width tokenCount current next
        argument) selected
  have hinternal := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsAppendTwoShiftedFormula tokenTable width tokenCount current next
        argument) selected _ hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘1’ : ValuationTerm) modeCertificate
      ((termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
            next argument) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeTwoFormula tokenTable width tokenCount current next
          mode binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount ⋎
        (termRowsModeFourFormula tokenTable width tokenCount current next mode
            tag argument consumedCount ⋎
          (termRowsModeFiveFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessCount ⋎
            termRowsOtherFormula tokenTable width tokenCount current next mode
              consumedCount))) modeFull
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) selectedPath
  have hmodes :=
    termRowsModeOnePathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeTwoLowerBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 2)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity)
    (hrows : CompactFormulaTransformOutputWitnessRows tokenTable width
      tokenCount current next witnessStart witnessFinish witnessCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeTwoLower hcount hconsumed hmode hguard hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeTwoLower hcount hconsumed hmode hguard hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation) hmode
  let guardCertificate := zeroTagGuardCertificate consumedCount tag argument
    binderArity hguard
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount witnessStart witnessFinish witnessCount
      next.parserFinish next.finish next.outputCount hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo termRowsZeroValuation) hmode
  have hguardResource :=
    zeroTagGuardCertificate_structuralPayloadBound_le_transparent consumedCount
      tag argument binderArity hguard
  have hrowsResource :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount witnessStart witnessFinish witnessCount
      next.parserFinish next.finish next.outputCount hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    guardCertificate rowsCertificate _ _ hguardResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount) selected
  have hinternal := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount) selected _ hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘2’ : ValuationTerm) modeCertificate
      ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsWitnessFormula tokenTable width tokenCount current next
            witnessStart witnessFinish witnessCount) ⋎
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeFourFormula tokenTable width tokenCount current next
          mode tag argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount)) modeFull
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) selectedPath
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsModeTwoPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeTwoRawBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 2)
    (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeTwoRaw hcount hconsumed hmode failure hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeTwoRaw hcount hconsumed hmode failure hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation) hmode
  let failureCertificate := tripleFailureCertificateFromData consumedCount tag
    argument binderArity failure
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo termRowsZeroValuation) hmode
  have hfailureResource :=
    tripleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag argument binderArity failure
  have hrowsResource :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    failureCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    failureCertificate rowsCertificate _ _ hfailureResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsGuardZeroTagFormula consumedCount tag argument
        binderArity ⋏
      termRowsWitnessFormula tokenTable width tokenCount current next
        witnessStart witnessFinish witnessCount) selected
  have hinternal := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsGuardZeroTagFormula consumedCount tag argument
        binderArity ⋏
      termRowsWitnessFormula tokenTable width tokenCount current next
        witnessStart witnessFinish witnessCount) selected _ hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘2’ : ValuationTerm) modeCertificate
      ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
          termRowsWitnessFormula tokenTable width tokenCount current next
            witnessStart witnessFinish witnessCount) ⋎
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeFourFormula tokenTable width tokenCount current next
          mode tag argument consumedCount ⋎
        (termRowsModeFiveFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessCount ⋎
          termRowsOtherFormula tokenTable width tokenCount current next mode
            consumedCount)) modeFull
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) selectedPath
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsModeTwoPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeFourOneBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 4)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputOneValueRows tokenTable width
      tokenCount current next argument) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFourOne hcount hconsumed hmode hguard hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFourOne hcount hconsumed hmode hguard hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 4
    (‘4’ : ValuationTerm) (termValue_arithmeticFour zeroValuation) hmode
  let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount argument hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 4 (‘4’ : ValuationTerm)
      (termValue_arithmeticFour termRowsZeroValuation) hmode
  have hguardResource :=
    oneTagGuardCertificate_structuralPayloadBound_le_transparent consumedCount
      tag hguard
  have hrowsResource :=
    compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount argument hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    guardCertificate rowsCertificate _ _ hguardResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsSameFormula tokenTable width tokenCount current next) selected
  have hinternal := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsSameFormula tokenTable width tokenCount current next) selected _
    hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm) modeCertificate
      ((termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsOneValueFormula tokenTable width tokenCount current next
            argument) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsSameFormula tokenTable width tokenCount current next))
      internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeFiveFormula tokenTable width tokenCount current next
          mode binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount) modeFull
  let afterTwo :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount) selectedPath
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) afterTwo
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsModeFourPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeFourSameBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 4)
    (failure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFourSame hcount hconsumed hmode failure hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFourSame hcount hconsumed hmode failure hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 4
    (‘4’ : ValuationTerm) (termValue_arithmeticFour zeroValuation) hmode
  let failureCertificate := doubleFailureCertificateFromData consumedCount tag
    failure
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 4 (‘4’ : ValuationTerm)
      (termValue_arithmeticFour termRowsZeroValuation) hmode
  have hfailureResource :=
    doubleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag failure
  have hrowsResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    failureCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    failureCertificate rowsCertificate _ _ hfailureResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsOneValueFormula tokenTable width tokenCount current next argument)
    selected
  have hinternal := transparentHybridDisjunctionRightPayloadBound_le
    (left := termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsOneValueFormula tokenTable width tokenCount current next argument)
    selected _ hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm) modeCertificate
      ((termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsOneValueFormula tokenTable width tokenCount current next
            argument) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsSameFormula tokenTable width tokenCount current next))
      internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsModeFiveFormula tokenTable width tokenCount current next
          mode binderArity tag argument consumedCount witnessCount ⋎
        termRowsOtherFormula tokenTable width tokenCount current next mode
          consumedCount) modeFull
  let afterTwo :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount) selectedPath
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) afterTwo
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsModeFourPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeFiveCapturedBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 0 (binderArity + argument)) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFiveCaptured hcount hconsumed hmode hguard hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFiveCaptured hcount hconsumed hmode hguard hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 5
    (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
  let guardCertificate := capturedGuardCertificate consumedCount tag argument
    witnessCount hguard
  let capturedTerm := nativeAddTerm (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm argument)
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
      capturedTerm (termValue_arithmeticZero zeroValuation)
      (by
        simp [capturedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm]) hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 5 (‘5’ : ValuationTerm)
      (termValue_arithmeticFive termRowsZeroValuation) hmode
  have hguardResource :=
    capturedGuardCertificate_structuralPayloadBound_le_transparent
      consumedCount tag argument witnessCount hguard
  have hcapturedClosed : capturedTerm.freeVariables = ∅ :=
    nativeAddTerm_freeVariables_eq_empty _ _
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty argument)
  have hrowsResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
      capturedTerm arithmeticZeroTerm_freeVariables_eq_empty hcapturedClosed
      (termValue_arithmeticZero
        FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation)
      (by
        simp [capturedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm]) hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    guardCertificate rowsCertificate _ _ hguardResource hrowsResource
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      (termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) selected
  have hinternal := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      (termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount)) selected _ hselected
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm) modeCertificate
      ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
          termRowsCapturedFormula tokenTable width tokenCount current next
            binderArity argument) ⋎
        ((termRowsResidualGuardFormula consumedCount tag argument
              witnessCount ⋏
            compactFormulaTransformTermResidualExistsFormula tokenTable width
              tokenCount current next argument witnessCount) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount))) internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsOtherFormula tokenTable width tokenCount current next
        mode consumedCount) modeFull
  let afterFour :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeFourFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) selectedPath
  let afterTwo :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount) afterFour
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) afterTwo
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsModeFivePathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only [capturedTerm]
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeFiveResidualBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount residual : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ witnessCount <= argument)
    (hresidual : residual <= argument)
    (hequality : argument = witnessCount + residual)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 residual) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFiveResidual hcount hconsumed hmode hguard residual hresidual
            hequality hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFiveResidual hcount hconsumed hmode hguard residual hresidual
          hequality hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 5
    (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
  let guardCertificate := residualGuardCertificate consumedCount tag argument
    witnessCount hguard
  let residualCertificate :=
    compactFormulaTransformTermResidualExistsCertificate tokenTable width
      tokenCount current next argument witnessCount residual hresidual hequality
      hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 5 (‘5’ : ValuationTerm)
      (termValue_arithmeticFive termRowsZeroValuation) hmode
  have hguardResource :=
    residualGuardCertificate_structuralPayloadBound_le_transparent
      consumedCount tag argument witnessCount hguard
  have hresidualResource :=
    compactFormulaTransformTermResidualExistsCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next argument witnessCount residual
      hresidual hequality hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate residualCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    guardCertificate residualCertificate _ _ hguardResource hresidualResource
  let middle := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount) selected
  have hmiddle := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount) selected _ hselected
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left :=
      termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) middle
  have hinternal := transparentHybridDisjunctionRightPayloadBound_le
    (left :=
      termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) middle _ hmiddle
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm) modeCertificate
      ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
          termRowsCapturedFormula tokenTable width tokenCount current next
            binderArity argument) ⋎
        ((termRowsResidualGuardFormula consumedCount tag argument
              witnessCount ⋏
            compactFormulaTransformTermResidualExistsFormula tokenTable width
              tokenCount current next argument witnessCount) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount))) internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsOtherFormula tokenTable width tokenCount current next
        mode consumedCount) modeFull
  let afterFour :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeFourFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) selectedPath
  let afterTwo :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount) afterFour
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) afterTwo
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsModeFivePathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsModeFiveRawBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (failure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFiveRaw hcount hconsumed hmode failure hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFiveRaw hcount hconsumed hmode failure hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 5
    (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
  let failureCertificate := doubleFailureCertificateFromData consumedCount tag
    failure
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hmodeResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
      mode 5 (‘5’ : ValuationTerm)
      (termValue_arithmeticFive termRowsZeroValuation) hmode
  have hfailureResource :=
    doubleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag failure
  have hrowsResource :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    failureCertificate rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    failureCertificate rowsCertificate _ _ hfailureResource hrowsResource
  let middle := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left :=
      termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
        compactFormulaTransformTermResidualExistsFormula tokenTable width
          tokenCount current next argument witnessCount) selected
  have hmiddle := transparentHybridDisjunctionRightPayloadBound_le
    (left :=
      termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
        compactFormulaTransformTermResidualExistsFormula tokenTable width
          tokenCount current next argument witnessCount) selected _ hselected
  let internal := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left :=
      termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) middle
  have hinternal := transparentHybridDisjunctionRightPayloadBound_le
    (left :=
      termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) middle _ hmiddle
  let modeFull := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate internal
  have hmodeFull :=
    termRowsModeOuterCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm) modeCertificate
      ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
          termRowsCapturedFormula tokenTable width tokenCount current next
            binderArity argument) ⋎
        ((termRowsResidualGuardFormula consumedCount tag argument
              witnessCount ⋏
            compactFormulaTransformTermResidualExistsFormula tokenTable width
              tokenCount current next argument witnessCount) ⋎
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current next
              consumedCount))) internal _ hmodeResource hinternal
  let selectedPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := termRowsOtherFormula tokenTable width tokenCount current next
        mode consumedCount) modeFull
  let afterFour :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeFourFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) selectedPath
  let afterTwo :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount) afterFour
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) afterTwo
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsModeFivePathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeFull _ hmodeFull
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

theorem
    compactFormulaTransformTermOutputRowsOtherBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hzero : mode ≠ 0)
    (hone : mode ≠ 1)
    (htwo : mode ≠ 2)
    (hfour : mode ≠ 4)
    (hfive : mode ≠ 5)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.other hcount hconsumed hzero hone htwo hfour hfive hrows)) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.other hcount hconsumed hzero hone htwo hfour hfive hrows) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let otherCertificate := otherModesWithTailCertificate mode hzero hone htwo
    hfour hfive
    (termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount) rowsCertificate
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have hrowsResource :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  have hotherResource :=
    otherModesWithTailCertificate_structuralPayloadBound_le_transparent mode
      hzero hone htwo hfour hfive
      (termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount) rowsCertificate
      (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
        width tokenCount current.parserFinish current.finish
        current.outputCount current.start current.parserTokensFinish
        current.parserTokensCount consumedCount next.parserFinish next.finish
        next.outputCount hrows) hrowsResource
  let afterFive :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeFiveFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessCount)
      otherCertificate
  let afterFour :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeFourFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) afterFive
  let afterTwo :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeTwoFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount) afterFour
  let afterOne :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeOneFormula tokenTable width tokenCount current next
        mode tag argument consumedCount) afterTwo
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsModeZeroFormula tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount) afterOne
  have hmodes :=
    termRowsOtherPathCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount otherCertificate _
      hotherResource
  have htop :=
    termRowsPositiveSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount countCertificate
      positiveCertificate modesCertificate _ hcountResource hpositiveResource
      hmodes
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := termRowsZeroCaseFormula tokenTable width tokenCount current
            next consumedCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate modesCertificate))) <= _
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
  dsimp only
  exact htop

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
