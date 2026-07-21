import integration.FoundationCompactPAValuationAtomicCompiler
import integration.FoundationCompactPAValuationTermCompilerBounds
import integration.FoundationCompactPAClosedAtomicCompilerBounds

/-!
# Explicit payload bounds for the valuation atomic compiler

The resources here are functions only of the valuation, relation symbol, and
two source terms.  In particular, no final proof payload, source-proof
payload, or caller-provided length is an input coordinate.  Formula casts are
payload preserving, while every real context connective is charged through
its published full-assembly cost.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAValuationAtomicCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.ClosedPAAtomicLiteral
open FoundationCompactPAClosedAtomicCompilerBounds
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.ClosedPAAtomicLiteralBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationAtomicCompiler

/-- Closed positive source cost, selected explicitly by the only two binary
PA relation symbols. -/
def positiveRelationSourcePayloadResource
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) : Nat :=
  match relationSymbol with
  | .eq =>
      ClosedPAAtomicLiteralBounds.payloadPolynomial
        (.equality (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1))))
  | .lt =>
      ClosedPAAtomicLiteralBounds.payloadPolynomial
        (.lessThan (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1))))

/-- Closed negative source cost, selected explicitly by relation symbol. -/
def negativeRelationSourcePayloadResource
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) : Nat :=
  match relationSymbol with
  | .eq =>
      ClosedPAAtomicLiteralBounds.payloadPolynomial
        (.disequality (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1))))
  | .lt =>
      ClosedPAAtomicLiteralBounds.payloadPolynomial
        (.notLessThan (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1))))

/-- Proof-free resource for the positive relation compiler.  The two term
equalities each pay their own contextual weakening; the closed source pays
its contextual weakening before the relation transport and final MP. -/
def compilePositiveRelationPayloadResource
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) : Nat :=
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables
    valuation
  let firstTerm := shortBinaryNumeralTerm (termValue valuation (args 0))
  let secondTerm := shortBinaryNumeralTerm (termValue valuation (args 1))
  let firstFormula :=
    (“!!firstTerm = !!(args 0)” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!(args 1)” : LO.FirstOrder.ArithmeticProposition)
  let firstBound := compileTermValueEqualityPayloadResource valuation (args 0) +
    weakeningFullAssemblyCost (insert firstFormula Gamma)
  let secondBound := compileTermValueEqualityPayloadResource valuation (args 1) +
    weakeningFullAssemblyCost (insert secondFormula Gamma)
  let sourceFormula := binaryRelationFormula relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol (args 0) (args 1)
  let contextualSourceBound :=
    positiveRelationSourcePayloadResource valuation relationSymbol args +
      weakeningFullAssemblyCost (insert sourceFormula Gamma)
  let transportBound := relationTransportImplicationStructuralPayloadBound
    Gamma relationSymbol firstTerm secondTerm (args 0) (args 1)
    firstBound secondBound
  transportBound + contextualSourceBound +
    contextualModusPonensFullAssemblyCost Gamma sourceFormula targetFormula

/-- Proof-free resource for the negative relation compiler.  In addition to
the positive branch's two forward equalities, it pays both equality
symmetries, reverse transport, and contextual modus tollens. -/
def compileNegativeRelationPayloadResource
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) : Nat :=
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables
    valuation
  let firstTerm := shortBinaryNumeralTerm (termValue valuation (args 0))
  let secondTerm := shortBinaryNumeralTerm (termValue valuation (args 1))
  let firstFormula :=
    (“!!firstTerm = !!(args 0)” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!(args 1)” : LO.FirstOrder.ArithmeticProposition)
  let firstForwardBound :=
    compileTermValueEqualityPayloadResource valuation (args 0) +
      weakeningFullAssemblyCost (insert firstFormula Gamma)
  let secondForwardBound :=
    compileTermValueEqualityPayloadResource valuation (args 1) +
      weakeningFullAssemblyCost (insert secondFormula Gamma)
  let firstReverseBound := contextualEqualitySymmetryStructuralPayloadBound
    Gamma firstTerm (args 0) firstForwardBound
  let secondReverseBound := contextualEqualitySymmetryStructuralPayloadBound
    Gamma secondTerm (args 1) secondForwardBound
  let sourceFormula := binaryRelationFormula relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol (args 0) (args 1)
  let reverseTransportBound := relationTransportImplicationStructuralPayloadBound
    Gamma relationSymbol (args 0) (args 1) firstTerm secondTerm
    firstReverseBound secondReverseBound
  let contextualSourceBound :=
    negativeRelationSourcePayloadResource valuation relationSymbol args +
      weakeningFullAssemblyCost (insert (∼sourceFormula) Gamma)
  reverseTransportBound + contextualSourceBound +
    CertifiedPAContextProof.modusTollensFullAssemblyCost
      Gamma targetFormula sourceFormula

theorem compilePositiveRelation_payloadLength_le_resource
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (htruth : formulaValue valuation
      (LO.FirstOrder.Semiformula.rel relationSymbol args)) :
    (compilePositiveRelation valuation relationSymbol args htruth).payloadLength <=
      compilePositiveRelationPayloadResource valuation relationSymbol args := by
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables
    valuation
  let firstRaw := compileTermValueEquality valuation (args 0)
  let secondRaw := compileTermValueEquality valuation (args 1)
  have hfirstVariables : (args 0).freeVariables ⊆
      (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables :=
    termFreeVariables_subset_relation relationSymbol args 0
  have hsecondVariables : (args 1).freeVariables ⊆
      (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables :=
    termFreeVariables_subset_relation relationSymbol args 1
  let firstEquality := CertifiedPAContextProof.weakenContext firstRaw
    (valuationContext_mono valuation hfirstVariables)
  let secondEquality := CertifiedPAContextProof.weakenContext secondRaw
    (valuationContext_mono valuation hsecondVariables)
  let sourceProof : CertifiedPAProof
      (binaryRelationFormula relationSymbol
        (shortBinaryNumeralTerm (termValue valuation (args 0)))
        (shortBinaryNumeralTerm (termValue valuation (args 1)))) := by
    cases relationSymbol with
    | eq =>
        have hvalue : termValue valuation (args 0) =
            termValue valuation (args 1) := by
          change (LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.eq
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.equality
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            binaryRelationFormula Language.Eq.eq
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact (binaryRelationFormula_eq_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
    | lt =>
        have hvalue : termValue valuation (args 0) <
            termValue valuation (args 1) := by
          change (LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.lt
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.lessThan
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            binaryRelationFormula Language.ORing.Rel.lt
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact (binaryRelationFormula_lt_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
  let contextualSource := CertifiedPAContextProof.weakenCertified Gamma
    sourceProof
  let transport := relationTransportImplicationFromEqualities relationSymbol
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
    (args 0) (args 1) firstEquality secondEquality
  let result := CertifiedPAContextProof.modusPonens transport contextualSource
  let firstTerm := shortBinaryNumeralTerm (termValue valuation (args 0))
  let secondTerm := shortBinaryNumeralTerm (termValue valuation (args 1))
  let firstFormula :=
    (“!!firstTerm = !!(args 0)” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!(args 1)” : LO.FirstOrder.ArithmeticProposition)
  let sourceFormula := binaryRelationFormula relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol (args 0) (args 1)
  let firstBound := compileTermValueEqualityPayloadResource valuation (args 0) +
    weakeningFullAssemblyCost (insert firstFormula Gamma)
  let secondBound := compileTermValueEqualityPayloadResource valuation (args 1) +
    weakeningFullAssemblyCost (insert secondFormula Gamma)
  let contextualSourceBound :=
    positiveRelationSourcePayloadResource valuation relationSymbol args +
      weakeningFullAssemblyCost (insert sourceFormula Gamma)
  let transportBound := relationTransportImplicationStructuralPayloadBound
    Gamma relationSymbol firstTerm secondTerm (args 0) (args 1)
    firstBound secondBound
  have hfirstRaw := compileTermValueEquality_payloadLength_le_resource
    valuation (args 0)
  have hsecondRaw := compileTermValueEquality_payloadLength_le_resource
    valuation (args 1)
  have hfirstWeaken := CertifiedPAContextProof.weakenContext_payloadLength_le
    firstRaw (valuationContext_mono valuation hfirstVariables)
  have hsecondWeaken := CertifiedPAContextProof.weakenContext_payloadLength_le
    secondRaw (valuationContext_mono valuation hsecondVariables)
  have hfirst : firstEquality.payloadLength <= firstBound := by
    calc
      firstEquality.payloadLength <= firstRaw.payloadLength +
          weakeningFullAssemblyCost (insert firstFormula Gamma) := by
        simpa only [firstEquality, firstFormula] using hfirstWeaken
      _ <= compileTermValueEqualityPayloadResource valuation (args 0) +
          weakeningFullAssemblyCost (insert firstFormula Gamma) :=
        Nat.add_le_add_right hfirstRaw _
      _ = firstBound := by rfl
  have hsecond : secondEquality.payloadLength <= secondBound := by
    calc
      secondEquality.payloadLength <= secondRaw.payloadLength +
          weakeningFullAssemblyCost (insert secondFormula Gamma) := by
        simpa only [secondEquality, secondFormula] using hsecondWeaken
      _ <= compileTermValueEqualityPayloadResource valuation (args 1) +
          weakeningFullAssemblyCost (insert secondFormula Gamma) :=
        Nat.add_le_add_right hsecondRaw _
      _ = secondBound := by rfl
  have hsource : sourceProof.payloadLength <=
      positiveRelationSourcePayloadResource valuation relationSymbol args := by
    cases relationSymbol with
    | eq =>
        let literal := ClosedPAAtomicLiteral.equality
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        have hvalue : literal.Truth := by
          dsimp only [literal, ClosedPAAtomicLiteral.Truth, ClosedPATerm.value]
          change (LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.eq
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            binaryRelationFormula Language.Eq.eq
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact (binaryRelationFormula_eq_formula _ _).symm
        have hraw := ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
          literal hvalue
        change (CertifiedPAProof.cast hformula raw).payloadLength <= _
        rw [CertifiedPAProof.cast_payloadLength]
        simpa only [positiveRelationSourcePayloadResource] using hraw
    | lt =>
        let literal := ClosedPAAtomicLiteral.lessThan
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        have hvalue : literal.Truth := by
          dsimp only [literal, ClosedPAAtomicLiteral.Truth, ClosedPATerm.value]
          change (LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.lt
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            binaryRelationFormula Language.ORing.Rel.lt
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact (binaryRelationFormula_lt_formula _ _).symm
        have hraw := ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
          literal hvalue
        change (CertifiedPAProof.cast hformula raw).payloadLength <= _
        rw [CertifiedPAProof.cast_payloadLength]
        simpa only [positiveRelationSourcePayloadResource] using hraw
  have hcontextualSourceWeaken :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le Gamma sourceProof
  have hcontextualSource : contextualSource.payloadLength <=
      contextualSourceBound := by
    calc
      contextualSource.payloadLength <= sourceProof.payloadLength +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
        simpa only [contextualSource, sourceFormula] using hcontextualSourceWeaken
      _ <= positiveRelationSourcePayloadResource valuation relationSymbol args +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) :=
        Nat.add_le_add_right hsource _
      _ = contextualSourceBound := by rfl
  have htransportRaw := relationTransportImplicationFromEqualities_payloadLength_le
    relationSymbol firstTerm secondTerm (args 0) (args 1)
    firstEquality secondEquality
  have htransport : transport.payloadLength <= transportBound := by
    exact htransportRaw.trans
      (relationTransportImplicationStructuralPayloadBound_mono
        Gamma relationSymbol firstTerm secondTerm (args 0) (args 1)
        hfirst hsecond)
  have hmp := CertifiedPAContextProof.modusPonens_payloadLength_le
    transport contextualSource
  let finalFormula := binaryRelationFormula_eq_relation relationSymbol args
  calc
    (compilePositiveRelation valuation relationSymbol args htruth).payloadLength =
        (CertifiedPAContextProof.cast finalFormula result).payloadLength := by rfl
    _ = result.payloadLength :=
      CertifiedPAContextProof.cast_payloadLength finalFormula result
    _ <= transport.payloadLength + contextualSource.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma sourceFormula targetFormula := by
      simpa only [result, sourceFormula, targetFormula] using hmp
    _ <= transportBound + contextualSourceBound +
        contextualModusPonensFullAssemblyCost Gamma sourceFormula targetFormula :=
      Nat.add_le_add_right (Nat.add_le_add htransport hcontextualSource) _
    _ = compilePositiveRelationPayloadResource valuation relationSymbol args := by
      rfl

theorem compileNegativeRelation_payloadLength_le_resource
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (htruth : formulaValue valuation
      (LO.FirstOrder.Semiformula.nrel relationSymbol args)) :
    (compileNegativeRelation valuation relationSymbol args htruth).payloadLength <=
      compileNegativeRelationPayloadResource valuation relationSymbol args := by
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables
    valuation
  let firstForwardRaw := compileTermValueEquality valuation (args 0)
  let secondForwardRaw := compileTermValueEquality valuation (args 1)
  have hfirstVariables : (args 0).freeVariables ⊆
      (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables :=
    termFreeVariables_subset_negatedRelation relationSymbol args 0
  have hsecondVariables : (args 1).freeVariables ⊆
      (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables :=
    termFreeVariables_subset_negatedRelation relationSymbol args 1
  let firstForward := CertifiedPAContextProof.weakenContext firstForwardRaw
    (valuationContext_mono valuation hfirstVariables)
  let secondForward := CertifiedPAContextProof.weakenContext secondForwardRaw
    (valuationContext_mono valuation hsecondVariables)
  let firstBackward := CertifiedPAContextProof.equalitySymmetry
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (args 0) firstForward
  let secondBackward := CertifiedPAContextProof.equalitySymmetry
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
    (args 1) secondForward
  let sourceProof : CertifiedPAProof
      (∼binaryRelationFormula relationSymbol
        (shortBinaryNumeralTerm (termValue valuation (args 0)))
        (shortBinaryNumeralTerm (termValue valuation (args 1)))) := by
    cases relationSymbol with
    | eq =>
        have hvalue : termValue valuation (args 0) ≠
            termValue valuation (args 1) := by
          change ¬(LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.eq
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.disequality
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            ∼binaryRelationFormula Language.Eq.eq
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact congrArg (fun formula : ValuationFormula => ∼formula)
            (binaryRelationFormula_eq_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
    | lt =>
        have hvalue : ¬termValue valuation (args 0) <
            termValue valuation (args 1) := by
          change ¬(LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.lt
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.notLessThan
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            ∼binaryRelationFormula Language.ORing.Rel.lt
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact congrArg (fun formula : ValuationFormula => ∼formula)
            (binaryRelationFormula_lt_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
  let contextualSource := CertifiedPAContextProof.weakenCertified Gamma
    sourceProof
  let reverseTransport := relationTransportImplicationFromEqualities
    relationSymbol (args 0) (args 1)
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
    firstBackward secondBackward
  let result := CertifiedPAContextProof.modusTollens
    reverseTransport contextualSource
  let firstTerm := shortBinaryNumeralTerm (termValue valuation (args 0))
  let secondTerm := shortBinaryNumeralTerm (termValue valuation (args 1))
  let firstFormula :=
    (“!!firstTerm = !!(args 0)” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!(args 1)” : LO.FirstOrder.ArithmeticProposition)
  let sourceFormula := binaryRelationFormula relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol (args 0) (args 1)
  let firstForwardBound :=
    compileTermValueEqualityPayloadResource valuation (args 0) +
      weakeningFullAssemblyCost (insert firstFormula Gamma)
  let secondForwardBound :=
    compileTermValueEqualityPayloadResource valuation (args 1) +
      weakeningFullAssemblyCost (insert secondFormula Gamma)
  let firstBackwardBound := contextualEqualitySymmetryStructuralPayloadBound
    Gamma firstTerm (args 0) firstForwardBound
  let secondBackwardBound := contextualEqualitySymmetryStructuralPayloadBound
    Gamma secondTerm (args 1) secondForwardBound
  let reverseTransportBound := relationTransportImplicationStructuralPayloadBound
    Gamma relationSymbol (args 0) (args 1) firstTerm secondTerm
    firstBackwardBound secondBackwardBound
  let contextualSourceBound :=
    negativeRelationSourcePayloadResource valuation relationSymbol args +
      weakeningFullAssemblyCost (insert (∼sourceFormula) Gamma)
  have hfirstForwardRaw := compileTermValueEquality_payloadLength_le_resource
    valuation (args 0)
  have hsecondForwardRaw := compileTermValueEquality_payloadLength_le_resource
    valuation (args 1)
  have hfirstForwardWeaken :=
    CertifiedPAContextProof.weakenContext_payloadLength_le firstForwardRaw
      (valuationContext_mono valuation hfirstVariables)
  have hsecondForwardWeaken :=
    CertifiedPAContextProof.weakenContext_payloadLength_le secondForwardRaw
      (valuationContext_mono valuation hsecondVariables)
  have hfirstForward : firstForward.payloadLength <= firstForwardBound := by
    calc
      firstForward.payloadLength <= firstForwardRaw.payloadLength +
          weakeningFullAssemblyCost (insert firstFormula Gamma) := by
        simpa only [firstForward, firstFormula] using hfirstForwardWeaken
      _ <= compileTermValueEqualityPayloadResource valuation (args 0) +
          weakeningFullAssemblyCost (insert firstFormula Gamma) :=
        Nat.add_le_add_right hfirstForwardRaw _
      _ = firstForwardBound := by rfl
  have hsecondForward : secondForward.payloadLength <= secondForwardBound := by
    calc
      secondForward.payloadLength <= secondForwardRaw.payloadLength +
          weakeningFullAssemblyCost (insert secondFormula Gamma) := by
        simpa only [secondForward, secondFormula] using hsecondForwardWeaken
      _ <= compileTermValueEqualityPayloadResource valuation (args 1) +
          weakeningFullAssemblyCost (insert secondFormula Gamma) :=
        Nat.add_le_add_right hsecondForwardRaw _
      _ = secondForwardBound := by rfl
  have hfirstBackward : firstBackward.payloadLength <= firstBackwardBound :=
    contextualEqualitySymmetry_payloadLength_le_structuralBound
      firstTerm (args 0) firstForward firstForwardBound hfirstForward
  have hsecondBackward : secondBackward.payloadLength <= secondBackwardBound :=
    contextualEqualitySymmetry_payloadLength_le_structuralBound
      secondTerm (args 1) secondForward secondForwardBound hsecondForward
  have hsource : sourceProof.payloadLength <=
      negativeRelationSourcePayloadResource valuation relationSymbol args := by
    cases relationSymbol with
    | eq =>
        let literal := ClosedPAAtomicLiteral.disequality
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        have hvalue : literal.Truth := by
          dsimp only [literal, ClosedPAAtomicLiteral.Truth, ClosedPATerm.value]
          change ¬(LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.eq
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            ∼binaryRelationFormula Language.Eq.eq
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact congrArg (fun formula : ValuationFormula => ∼formula)
            (binaryRelationFormula_eq_formula _ _).symm
        have hraw := ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
          literal hvalue
        change (CertifiedPAProof.cast hformula raw).payloadLength <= _
        rw [CertifiedPAProof.cast_payloadLength]
        simpa only [negativeRelationSourcePayloadResource] using hraw
    | lt =>
        let literal := ClosedPAAtomicLiteral.notLessThan
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        have hvalue : literal.Truth := by
          dsimp only [literal, ClosedPAAtomicLiteral.Truth, ClosedPATerm.value]
          change ¬(LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.lt
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            ∼binaryRelationFormula Language.ORing.Rel.lt
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact congrArg (fun formula : ValuationFormula => ∼formula)
            (binaryRelationFormula_lt_formula _ _).symm
        have hraw := ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
          literal hvalue
        change (CertifiedPAProof.cast hformula raw).payloadLength <= _
        rw [CertifiedPAProof.cast_payloadLength]
        simpa only [negativeRelationSourcePayloadResource] using hraw
  have hcontextualSourceWeaken :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le Gamma sourceProof
  have hcontextualSource : contextualSource.payloadLength <=
      contextualSourceBound := by
    calc
      contextualSource.payloadLength <= sourceProof.payloadLength +
          weakeningFullAssemblyCost (insert (∼sourceFormula) Gamma) := by
        simpa only [contextualSource, sourceFormula] using hcontextualSourceWeaken
      _ <= negativeRelationSourcePayloadResource valuation relationSymbol args +
          weakeningFullAssemblyCost (insert (∼sourceFormula) Gamma) :=
        Nat.add_le_add_right hsource _
      _ = contextualSourceBound := by rfl
  have hreverseTransportRaw :=
    relationTransportImplicationFromEqualities_payloadLength_le
      relationSymbol (args 0) (args 1) firstTerm secondTerm
      firstBackward secondBackward
  have hreverseTransport : reverseTransport.payloadLength <=
      reverseTransportBound := by
    exact hreverseTransportRaw.trans
      (relationTransportImplicationStructuralPayloadBound_mono
        Gamma relationSymbol (args 0) (args 1) firstTerm secondTerm
        hfirstBackward hsecondBackward)
  have hmt := CertifiedPAContextProof.modusTollens_payloadLength_le
    reverseTransport contextualSource
  let finalFormula :=
    negatedBinaryRelationFormula_eq_negatedRelation relationSymbol args
  calc
    (compileNegativeRelation valuation relationSymbol args htruth).payloadLength =
        (CertifiedPAContextProof.cast finalFormula result).payloadLength := by rfl
    _ = result.payloadLength :=
      CertifiedPAContextProof.cast_payloadLength finalFormula result
    _ <= reverseTransport.payloadLength + contextualSource.payloadLength +
        CertifiedPAContextProof.modusTollensFullAssemblyCost
          Gamma targetFormula sourceFormula := by
      simpa only [result, targetFormula, sourceFormula] using hmt
    _ <= reverseTransportBound + contextualSourceBound +
        CertifiedPAContextProof.modusTollensFullAssemblyCost
          Gamma targetFormula sourceFormula :=
      Nat.add_le_add_right
        (Nat.add_le_add hreverseTransport hcontextualSource) _
    _ = compileNegativeRelationPayloadResource valuation relationSymbol args := by
      rfl

/-! ## Fixed polynomial endpoint -/

/-- Fixed univariate endpoint shared by positive and negative atomic
valuation compilation. -/
def valuationAtomicCompilerPayloadPolynomial (resource : Nat) : Nat :=
  resource * resource + 2 * resource + 1

theorem resource_le_valuationAtomicCompilerPayloadPolynomial
    (resource : Nat) :
    resource <= valuationAtomicCompilerPayloadPolynomial resource := by
  unfold valuationAtomicCompilerPayloadPolynomial
  calc
    resource <= 2 * resource := by omega
    _ <= resource * resource + 2 * resource := Nat.le_add_left _ _
    _ <= resource * resource + 2 * resource + 1 := Nat.le_add_right _ _

theorem compilePositiveRelationPayloadResource_le_fixedPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) :
    compilePositiveRelationPayloadResource valuation relationSymbol args <=
      valuationAtomicCompilerPayloadPolynomial
        (compilePositiveRelationPayloadResource valuation relationSymbol args) :=
  resource_le_valuationAtomicCompilerPayloadPolynomial _

theorem compileNegativeRelationPayloadResource_le_fixedPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) :
    compileNegativeRelationPayloadResource valuation relationSymbol args <=
      valuationAtomicCompilerPayloadPolynomial
        (compileNegativeRelationPayloadResource valuation relationSymbol args) :=
  resource_le_valuationAtomicCompilerPayloadPolynomial _

theorem compilePositiveRelation_payloadLength_le_fixedPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (htruth : formulaValue valuation
      (LO.FirstOrder.Semiformula.rel relationSymbol args)) :
    (compilePositiveRelation valuation relationSymbol args htruth).payloadLength <=
      valuationAtomicCompilerPayloadPolynomial
        (compilePositiveRelationPayloadResource valuation relationSymbol args) :=
  (compilePositiveRelation_payloadLength_le_resource
    valuation relationSymbol args htruth).trans
    (compilePositiveRelationPayloadResource_le_fixedPolynomial
      valuation relationSymbol args)

theorem compileNegativeRelation_payloadLength_le_fixedPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (htruth : formulaValue valuation
      (LO.FirstOrder.Semiformula.nrel relationSymbol args)) :
    (compileNegativeRelation valuation relationSymbol args htruth).payloadLength <=
      valuationAtomicCompilerPayloadPolynomial
        (compileNegativeRelationPayloadResource valuation relationSymbol args) :=
  (compileNegativeRelation_payloadLength_le_resource
    valuation relationSymbol args htruth).trans
    (compileNegativeRelationPayloadResource_le_fixedPolynomial
      valuation relationSymbol args)

#print axioms positiveRelationSourcePayloadResource
#print axioms negativeRelationSourcePayloadResource
#print axioms compilePositiveRelation_payloadLength_le_resource
#print axioms compileNegativeRelation_payloadLength_le_resource
#print axioms compilePositiveRelation_payloadLength_le_fixedPolynomial
#print axioms compileNegativeRelation_payloadLength_le_fixedPolynomial

end FoundationCompactPAValuationAtomicCompilerBounds
