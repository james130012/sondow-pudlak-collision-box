import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds

/-!
# Public resource for a complete fixed-width entry certificate

This endpoint combines the witness guard, binary-length graph, size guard,
and bounded bitwise universal certificate without caller-supplied proof
payload resources.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 150000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPABinaryLengthValuationContextCompilerBounds
open FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
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

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def fixedWidthWitnessGuardStructuralPayloadPolynomial
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  compilePositiveRelationPayloadPolynomial valuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm size, (‘!!valueTerm + 1’ : ValuationTerm)]

private theorem fixedWidthWitnessGuardHybridCertificate_structuralPayloadBound_eq
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthWitnessGuardHybridCertificate valuation valueTerm) =
      compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm
            (Nat.size (termValue valuation valueTerm)),
          (‘!!valueTerm + 1’ : ValuationTerm)] := by
  rfl

theorem
    fixedWidthWitnessGuardHybridCertificate_structuralPayloadBound_le_public
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm)
    (hvalue : valueTerm.freeVariables = ∅) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthWitnessGuardHybridCertificate valuation valueTerm) ≤
      fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm := by
  let size := Nat.size (termValue valuation valueTerm)
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm size, (‘!!valueTerm + 1’ : ValuationTerm)]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm size).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change (‘!!valueTerm + 1’ : ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticAddTerm_freeVariables, hvalue,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hresource :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      valuation Language.ORing.Rel.lt args hfirst hsecond
  rw [fixedWidthWitnessGuardHybridCertificate_structuralPayloadBound_eq]
  unfold fixedWidthWitnessGuardStructuralPayloadPolynomial
  dsimp only [size, args] at hresource ⊢
  exact hresource

def fixedWidthLengthStructuralPayloadPolynomial
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  compileBinaryLengthAtValuationPayloadPolynomial valuation
    (shortBinaryNumeralTerm size) valueTerm

private theorem fixedWidthLengthHybridCertificate_structuralPayloadBound_eq
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthLengthHybridCertificate valuation valueTerm) =
      compileBinaryLengthAtValuationPayloadResource valuation
        (shortBinaryNumeralTerm
          (Nat.size (termValue valuation valueTerm))) valueTerm := by
  rfl

theorem fixedWidthLengthHybridCertificate_structuralPayloadBound_le_public
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm)
    (hvalue : valueTerm.freeVariables = ∅) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthLengthHybridCertificate valuation valueTerm) ≤
      fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm := by
  let size := Nat.size (termValue valuation valueTerm)
  have hsizeTerm :
      (shortBinaryNumeralTerm size).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hvalueTerm : valueTerm.freeVariables ⊆ {0} := by
    rw [hvalue]
    simp
  have hresource :=
    compileBinaryLengthAtValuationPayloadResource_le_publicPolynomial
      valuation (shortBinaryNumeralTerm size) valueTerm
      hsizeTerm hvalueTerm
  rw [fixedWidthLengthHybridCertificate_structuralPayloadBound_eq]
  unfold fixedWidthLengthStructuralPayloadPolynomial
  dsimp only [size] at hresource ⊢
  exact hresource

def fixedWidthSizeGuardStructuralPayloadPolynomial
    (valuation : Nat -> Nat) (widthTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let sizeTerm : ValuationTerm := shortBinaryNumeralTerm size
  let args : Fin 2 -> ValuationTerm := ![sizeTerm, widthTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  compilePositiveRelationPayloadPolynomial valuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      valuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem
    fixedWidthSizeGuardHybridCertificate_structuralPayloadBound_le_public
    (valuation : Nat -> Nat) (widthTerm valueTerm : ValuationTerm)
    (hwidth : widthTerm.freeVariables = ∅)
    (hsize : Nat.size (termValue valuation valueTerm) ≤
      termValue valuation widthTerm) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthSizeGuardHybridCertificate valuation widthTerm valueTerm
          hsize) ≤
      fixedWidthSizeGuardStructuralPayloadPolynomial
        valuation widthTerm valueTerm := by
  let size := Nat.size (termValue valuation valueTerm)
  let sizeTerm : ValuationTerm := shortBinaryNumeralTerm size
  let args : Fin 2 -> ValuationTerm := ![sizeTerm, widthTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm size).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change widthTerm.freeVariables ⊆ {0}
    rw [hwidth]
    simp
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      valuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      valuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases hequal : size = termValue valuation widthTerm
  · dsimp only [size] at hequal
    simp only [fixedWidthSizeGuardHybridCertificate]
    rw [dif_pos hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold fixedWidthSizeGuardStructuralPayloadPolynomial
    dsimp only [size, sizeTerm, args] at hequality hstrict ⊢
    omega
  · dsimp only [size] at hequal
    simp only [fixedWidthSizeGuardHybridCertificate]
    rw [dif_neg hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold fixedWidthSizeGuardStructuralPayloadPolynomial
    dsimp only [size, sizeTerm, args] at hequality hstrict ⊢
    omega

def hybridConjunctionStructuralPayloadEnvelope
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource rightResource : Nat) : Nat :=
  let Gamma := valuationContext (left ⋏ right).freeVariables valuation
  leftResource + weakeningFullAssemblyCost (insert left Gamma) +
    rightResource + weakeningFullAssemblyCost (insert right Gamma) +
    conjunctionFullAssemblyCost Gamma left right

theorem hybridConjunctionStructuralPayloadBound_le_envelope
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (leftResource rightResource : Nat)
    (hleft : hybridFormulaStructuralPayloadBound leftCertificate ≤
      leftResource)
    (hright : hybridFormulaStructuralPayloadBound rightCertificate ≤
      rightResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate) ≤
      hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftResource rightResource := by
  simp only [hybridFormulaStructuralPayloadBound]
  unfold hybridConjunctionStructuralPayloadEnvelope
  dsimp only
  omega

def hybridExistsWitnessStructuralPayloadEnvelope
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness bodyResource : Nat) : Nat :=
  let formula := (∃⁰ body : ValuationFormula)
  let instantiated := body/[shortBinaryNumeralTerm witness]
  let Gamma := valuationContext formula.freeVariables valuation
  bodyResource + weakeningFullAssemblyCost (insert instantiated Gamma) +
    existsIntroFullAssemblyCost Gamma body (shortBinaryNumeralTerm witness)

theorem hybridExistsWitnessStructuralPayloadBound_le_envelope
    {valuation : Nat -> Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat)
    (bodyCertificate : CheckedHybridValuationBoundedFormulaCertificate
      valuation (body/[shortBinaryNumeralTerm witness]))
    (bodyResource : Nat)
    (hbody : hybridFormulaStructuralPayloadBound bodyCertificate ≤
      bodyResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
          body witness bodyCertificate) ≤
      hybridExistsWitnessStructuralPayloadEnvelope valuation body witness
        bodyResource := by
  simp only [hybridFormulaStructuralPayloadBound]
  unfold hybridExistsWitnessStructuralPayloadEnvelope
  dsimp only
  omega

def fixedWidthPostWitnessStructuralPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let guardFormula := fixedWidthWitnessGuard size valueTerm
  let lengthFormula := fixedWidthLengthFormula size valueTerm
  let sizeGuardFormula := fixedWidthSizeGuard size widthTerm
  let universalFormula := fixedWidthUniversalFormula
    tableTerm widthTerm indexTerm valueTerm
  let innerFormula := sizeGuardFormula ⋏ universalFormula
  let middleFormula := lengthFormula ⋏ innerFormula
  let innerResource := hybridConjunctionStructuralPayloadEnvelope valuation
    sizeGuardFormula universalFormula
    (fixedWidthSizeGuardStructuralPayloadPolynomial
      valuation widthTerm valueTerm)
    (fixedWidthUniversalStructuralPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)
  let middleResource := hybridConjunctionStructuralPayloadEnvelope valuation
    lengthFormula innerFormula
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    innerResource
  hybridConjunctionStructuralPayloadEnvelope valuation guardFormula
    middleFormula
    (fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm)
    middleResource

theorem
    compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_public
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationPostWitnessHybridCertificate
          valuation tableTerm widthTerm indexTerm valueTerm hentry) ≤
      fixedWidthPostWitnessStructuralPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
  let guardCertificate :=
    fixedWidthWitnessGuardHybridCertificate valuation valueTerm
  let lengthCertificate :=
    fixedWidthLengthHybridCertificate valuation valueTerm
  let sizeGuardCertificate := fixedWidthSizeGuardHybridCertificate
    valuation widthTerm valueTerm hentry.1
  let universalCertificate := fixedWidthUniversalHybridCertificate valuation
    tableTerm widthTerm indexTerm valueTerm hentry.2
  have hguard :=
    fixedWidthWitnessGuardHybridCertificate_structuralPayloadBound_le_public
      valuation valueTerm hvalue
  have hlength :=
    fixedWidthLengthHybridCertificate_structuralPayloadBound_le_public
      valuation valueTerm hvalue
  have hsizeGuard :=
    fixedWidthSizeGuardHybridCertificate_structuralPayloadBound_le_public
      valuation widthTerm valueTerm hwidth hentry.1
  have huniversal :=
    fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_publicPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
      hvalue hentry.2
  have hinner := hybridConjunctionStructuralPayloadBound_le_envelope
    sizeGuardCertificate universalCertificate
    (fixedWidthSizeGuardStructuralPayloadPolynomial
      valuation widthTerm valueTerm)
    (fixedWidthUniversalStructuralPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)
    hsizeGuard huniversal
  have hmiddle := hybridConjunctionStructuralPayloadBound_le_envelope
    lengthCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sizeGuardCertificate universalCertificate)
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    (hybridConjunctionStructuralPayloadEnvelope valuation
      (fixedWidthSizeGuard (Nat.size (termValue valuation valueTerm)) widthTerm)
      (fixedWidthUniversalFormula tableTerm widthTerm indexTerm valueTerm)
      (fixedWidthSizeGuardStructuralPayloadPolynomial
        valuation widthTerm valueTerm)
      (fixedWidthUniversalStructuralPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm))
    hlength hinner
  have hpost := hybridConjunctionStructuralPayloadBound_le_envelope
    guardCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      lengthCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        sizeGuardCertificate universalCertificate))
    (fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm)
    (hybridConjunctionStructuralPayloadEnvelope valuation
      (fixedWidthLengthFormula
        (Nat.size (termValue valuation valueTerm)) valueTerm)
      (fixedWidthSizeGuard
          (Nat.size (termValue valuation valueTerm)) widthTerm ⋏
        fixedWidthUniversalFormula tableTerm widthTerm indexTerm valueTerm)
      (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
      (hybridConjunctionStructuralPayloadEnvelope valuation
        (fixedWidthSizeGuard
          (Nat.size (termValue valuation valueTerm)) widthTerm)
        (fixedWidthUniversalFormula tableTerm widthTerm indexTerm valueTerm)
        (fixedWidthSizeGuardStructuralPayloadPolynomial
          valuation widthTerm valueTerm)
        (fixedWidthUniversalStructuralPayloadPolynomial valuation tableTerm
          widthTerm indexTerm valueTerm)))
    hguard hmiddle
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          lengthCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            sizeGuardCertificate universalCertificate))) ≤ _
  unfold fixedWidthPostWitnessStructuralPayloadPolynomial
  dsimp only
  exact hpost

def compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  hybridExistsWitnessStructuralPayloadEnvelope valuation body size
    (fixedWidthPostWitnessStructuralPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)

theorem
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          tableTerm widthTerm indexTerm valueTerm hentry) ≤
      compactFixedWidthEntryAtValuationStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  let postCertificate :=
    compactFixedWidthEntryAtValuationPostWitnessHybridCertificate valuation
      tableTerm widthTerm indexTerm valueTerm hentry
  let instantiated :=
    CheckedHybridValuationBoundedFormulaCertificate.cast
      (compactFixedWidthEntryAtValuationWitnessBody_subst
        tableTerm widthTerm indexTerm valueTerm size).symm postCertificate
  have hpost :=
    compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_public
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
      hvalue hentry
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated ≤
      fixedWidthPostWitnessStructuralPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body size instantiated
    (fixedWidthPostWitnessStructuralPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)
    hinstantiated
  simpa only [compactFixedWidthEntryAtValuationExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial,
    size, body, postCertificate, instantiated] using hexists
#print axioms
  fixedWidthWitnessGuardHybridCertificate_structuralPayloadBound_le_public
#print axioms
  fixedWidthLengthHybridCertificate_structuralPayloadBound_le_public
#print axioms
  fixedWidthSizeGuardHybridCertificate_structuralPayloadBound_le_public
#print axioms
  compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_public
#print axioms
  compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
