import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

/-!
# Transparent resources for fixed-width entries at open indices

The polynomial endpoint for closed coordinates is intentionally not reused at
an open universal-row index.  Instead this file removes proof-dependent branch
resources while retaining input-computable syntax and context costs exactly.
The resulting envelope is transparent but is not yet advertised as a fixed
polynomial in coordinate bit widths.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedCertifiedVerifier
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerLeafPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds

def hybridBranchesUniformStructuralPayloadEnvelope
    (totalBound : Nat)
    (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (leafBound : Nat) : Nat -> Nat
  | 0 =>
      let Gamma :=
        (valuationContext outerVariables valuation).image Rewriting.shift
      let target := Rewriting.free body
      FoundationCompactCertifiedContextProof.CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
          target +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert target
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (contextualFiniteBoundContext Gamma totalBound)))
  | bound + 1 =>
      let Gamma :=
        (valuationContext outerVariables valuation).image Rewriting.shift
      let target := Rewriting.free body
      let caseFormula := finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 bound) (&0)
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body leafBound bound +
        (leafBound +
          FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert target (insert (∼caseFormula) Gamma)) +
          FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert target
              (insert (∼caseFormula)
                (contextualFiniteBoundContext Gamma totalBound)))) +
        FoundationCompactCertifiedContextProof.CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
          (contextualFiniteBoundContext Gamma totalBound) target
          (finiteEqualityCases (&0) bound) caseFormula

theorem hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (totalBound : Nat) (outerVariables : Finset Nat) (leafBound : Nat) :
    {bound : Nat} ->
    (branches : CheckedHybridValuationUniversalBranches
      valuation body bound) ->
    HybridBranchesLeafPayloadBound leafBound branches ->
    hybridBranchesStructuralPayloadEnvelope totalBound outerVariables
        branches ≤
      hybridBranchesUniformStructuralPayloadEnvelope totalBound
        outerVariables valuation body leafBound bound
  | 0, .nil _ _, _ => by
      rfl
  | bound + 1, .snoc initial last, hleaves => by
      have hparts : HybridBranchesLeafPayloadBound leafBound initial ∧
          hybridFormulaStructuralPayloadBound last ≤ leafBound := by
        simpa only [HybridBranchesLeafPayloadBound] using hleaves
      have hinitial :=
        hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
          totalBound outerVariables leafBound initial hparts.1
      simp only [hybridBranchesStructuralPayloadEnvelope,
        hybridBranchesUniformStructuralPayloadEnvelope]
      omega

def contextualHybridUniversalFormulaCodeSum
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) : Nat :=
  Gamma.sum fun formula => (binaryFormulaCode formula).length

theorem formulaCode_le_contextualHybridUniversalFormulaCodeSum
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hformula : formula ∈ Gamma) :
    (binaryFormulaCode formula).length <=
      contextualHybridUniversalFormulaCodeSum Gamma := by
  unfold contextualHybridUniversalFormulaCodeSum
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (binaryFormulaCode candidate).length)
    hformula

def contextualHybridUniversalFormulaEnvelope
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  explicitHybridUniversalFormulaEnvelope bound body +
    contextualHybridUniversalFormulaCodeSum Gamma

def contextualHybridUniversalLocalPayloadEnvelope
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  smallContextAssemblyEnvelope
    (contextualHybridUniversalFormulaEnvelope Gamma bound body)

def contextualHybridUniversalBranchesPayloadPolynomial
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (totalBound caseCount : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (leafBound : Nat) : Nat :=
  (caseCount + 1) *
    (leafBound +
      3 * contextualHybridUniversalLocalPayloadEnvelope
        Gamma totalBound body)

theorem contextualHybridUniversalBaseAssemblyCost_le
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hGammaCard : Gamma.card <= 1) :
    CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
          (Rewriting.free body) +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert (Rewriting.free body)
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (contextualFiniteBoundContext Gamma bound))) <=
      2 * contextualHybridUniversalLocalPayloadEnvelope Gamma bound body := by
  let syntaxResource := explicitHybridUniversalSyntaxResource bound body
  let formulaEnvelope :=
    contextualHybridUniversalFormulaEnvelope Gamma bound body
  let target := Rewriting.free body
  have hsyntaxBound : bound <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold explicitHybridUniversalSyntaxResource
    omega
  have hexplicitEnvelope :
      explicitHybridUniversalFormulaEnvelope bound body <= formulaEnvelope := by
    dsimp only [formulaEnvelope]
    unfold contextualHybridUniversalFormulaEnvelope
    omega
  have hboundedEnvelope :
      boundedUniversalClosedFormulaEnvelope syntaxResource <=
        formulaEnvelope := by
    apply le_trans ?_ hexplicitEnvelope
    dsimp only [syntaxResource]
    unfold explicitHybridUniversalFormulaEnvelope
    omega
  have htarget : (binaryFormulaCode target).length <= formulaEnvelope := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [target, formulaEnvelope]
    unfold contextualHybridUniversalFormulaEnvelope
      explicitHybridUniversalFormulaEnvelope
    omega
  have hfalse :
      (binaryFormulaCode
        (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length <=
          formulaEnvelope := by
    exact (negatedFalse_code_le_boundedUniversal syntaxResource).trans
      hboundedEnvelope
  have hboundFormula :
      (binaryFormulaCode (∼finiteBoundFormula bound)).length <=
        formulaEnvelope := by
    exact (negatedFiniteBoundFormula_code_le_boundedUniversal
      bound syntaxResource hsyntaxBound).trans hboundedEnvelope
  have hGamma : FormulaCodeBound Gamma formulaEnvelope := by
    intro formula hformula
    exact (formulaCode_le_contextualHybridUniversalFormulaCodeSum
      hformula).trans (by
        dsimp only [formulaEnvelope]
        unfold contextualHybridUniversalFormulaEnvelope
        omega)
  have hcontext : FormulaCodeBound
      (contextualFiniteBoundContext Gamma bound) formulaEnvelope := by
    intro formula hformula
    simp only [contextualFiniteBoundContext, Finset.mem_insert] at hformula
    rcases hformula with rfl | hformula
    · exact hboundFormula
    · exact hGamma formula hformula
  have hweakContext : FormulaCodeBound
      (insert target
        (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
          (contextualFiniteBoundContext Gamma bound))) formulaEnvelope :=
    (hcontext.insert hfalse).insert htarget
  have hcontextCard :
      (contextualFiniteBoundContext Gamma bound).card <= 2 := by
    have hinsert := Finset.card_insert_le
      (∼finiteBoundFormula bound) Gamma
    simpa only [contextualFiniteBoundContext] using
      hinsert.trans (by omega)
  have hweakCard :
      (insert target
        (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
          (contextualFiniteBoundContext Gamma bound))).card <= 8 := by
    have hfirst := Finset.card_insert_le
      (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
      (contextualFiniteBoundContext Gamma bound)
    have hsecond := Finset.card_insert_le target
      (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
        (contextualFiniteBoundContext Gamma bound))
    omega
  have hexFalso := exFalsoAssumptionFullPayloadCost_le_small
    target formulaEnvelope htarget hfalse
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert target
      (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
        (contextualFiniteBoundContext Gamma bound)))
    formulaEnvelope hweakCard hweakContext
  unfold contextualHybridUniversalLocalPayloadEnvelope
  dsimp only [target, formulaEnvelope] at hexFalso hweakening ⊢
  omega

theorem contextualHybridUniversalStepAssemblyCost_le
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (totalBound index : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hGammaCard : Gamma.card <= 1)
    (hindex : index + 1 <= totalBound) :
    let target := Rewriting.free body
    let caseFormula := finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 index) (&0)
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
        (insert target (insert (∼caseFormula) Gamma)) +
      FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
        (insert target
          (insert (∼caseFormula)
            (contextualFiniteBoundContext Gamma totalBound))) +
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        (contextualFiniteBoundContext Gamma totalBound) target
        (finiteEqualityCases (&0) index) caseFormula <=
      3 * contextualHybridUniversalLocalPayloadEnvelope
        Gamma totalBound body := by
  let syntaxResource := explicitHybridUniversalSyntaxResource totalBound body
  let formulaEnvelope :=
    contextualHybridUniversalFormulaEnvelope Gamma totalBound body
  let target := Rewriting.free body
  let caseFormula := finiteCaseEqualityFormula
    (iteratedSuccessorTerm 0 index) (&0)
  have hsyntaxBound : totalBound <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold explicitHybridUniversalSyntaxResource
    omega
  have hexplicitEnvelope :
      explicitHybridUniversalFormulaEnvelope totalBound body <=
        formulaEnvelope := by
    dsimp only [formulaEnvelope]
    unfold contextualHybridUniversalFormulaEnvelope
    omega
  have hboundedEnvelope :
      boundedUniversalClosedFormulaEnvelope syntaxResource <=
        formulaEnvelope := by
    apply le_trans ?_ hexplicitEnvelope
    dsimp only [syntaxResource]
    unfold explicitHybridUniversalFormulaEnvelope
    omega
  have htarget : (binaryFormulaCode target).length <= formulaEnvelope := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [target, formulaEnvelope]
    unfold contextualHybridUniversalFormulaEnvelope
      explicitHybridUniversalFormulaEnvelope
    omega
  have hcase :
      (binaryFormulaCode (∼caseFormula)).length <= formulaEnvelope := by
    have hbase := negatedFiniteCaseEqualityFormula_code_le_boundedUniversal
      index syntaxResource (by omega)
    dsimp only [caseFormula]
    exact hbase.trans hboundedEnvelope
  have hGamma : FormulaCodeBound Gamma formulaEnvelope := by
    intro formula hformula
    exact (formulaCode_le_contextualHybridUniversalFormulaCodeSum
      hformula).trans (by
        dsimp only [formulaEnvelope]
        unfold contextualHybridUniversalFormulaEnvelope
        omega)
  have hboundFormula :
      (binaryFormulaCode (∼finiteBoundFormula totalBound)).length <=
        formulaEnvelope := by
    exact (negatedFiniteBoundFormula_code_le_boundedUniversal
      totalBound syntaxResource hsyntaxBound).trans hboundedEnvelope
  have hfiniteContext : FormulaCodeBound
      (contextualFiniteBoundContext Gamma totalBound) formulaEnvelope := by
    intro formula hformula
    simp only [contextualFiniteBoundContext, Finset.mem_insert] at hformula
    rcases hformula with rfl | hformula
    · exact hboundFormula
    · exact hGamma formula hformula
  have hweakOneBound : FormulaCodeBound
      (insert target (insert (∼caseFormula) Gamma)) formulaEnvelope :=
    (hGamma.insert hcase).insert htarget
  have hweakTwoBound : FormulaCodeBound
      (insert target
        (insert (∼caseFormula)
          (contextualFiniteBoundContext Gamma totalBound)))
      formulaEnvelope :=
    (hfiniteContext.insert hcase).insert htarget
  have hcontextCard :
      (contextualFiniteBoundContext Gamma totalBound).card <= 4 := by
    have hinsert := Finset.card_insert_le
      (∼finiteBoundFormula totalBound) Gamma
    simp only [contextualFiniteBoundContext]
    omega
  have hweakOneCard :
      (insert target (insert (∼caseFormula) Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le (∼caseFormula) Gamma
    have hsecond := Finset.card_insert_le target
      (insert (∼caseFormula) Gamma)
    omega
  have hweakTwoCard :
      (insert target
        (insert (∼caseFormula)
          (contextualFiniteBoundContext Gamma totalBound))).card <= 8 := by
    have hfirst := Finset.card_insert_le (∼caseFormula)
      (contextualFiniteBoundContext Gamma totalBound)
    have hsecond := Finset.card_insert_le target
      (insert (∼caseFormula)
        (contextualFiniteBoundContext Gamma totalBound))
    omega
  have hnegatedLeft :
      (binaryFormulaCode
        (∼finiteEqualityCases
          (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) index)).length <=
        formulaEnvelope := by
    exact (negatedFiniteEqualityCases_code_le_boundedUniversal
      index syntaxResource (by omega)).trans hboundedEnvelope
  have hnegatedDisjunction :
      (binaryFormulaCode
        (∼(finiteEqualityCases
          (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) index ⋎
            caseFormula))).length <=
          formulaEnvelope := by
    have hraw := negatedFiniteEqualityCases_code_le_boundedUniversal
      (index + 1) syntaxResource (by omega)
    have hraw' := hraw.trans hboundedEnvelope
    simpa only [caseFormula, finiteEqualityCases_succ] using hraw'
  have hweakOne := weakeningFullAssemblyCost_le_small
    (insert target (insert (∼caseFormula) Gamma))
    formulaEnvelope hweakOneCard hweakOneBound
  have hweakTwo := weakeningFullAssemblyCost_le_small
    (insert target
      (insert (∼caseFormula)
        (contextualFiniteBoundContext Gamma totalBound)))
    formulaEnvelope hweakTwoCard hweakTwoBound
  have heliminate :=
    eliminateDisjunctionAssumptionFullAssemblyCost_le_small
      (contextualFiniteBoundContext Gamma totalBound) target
      (finiteEqualityCases
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) index)
      caseFormula formulaEnvelope
      hcontextCard hfiniteContext htarget hnegatedLeft hcase
      hnegatedDisjunction
  unfold contextualHybridUniversalLocalPayloadEnvelope
  dsimp only [target, caseFormula, formulaEnvelope] at hweakOne hweakTwo heliminate ⊢
  omega

theorem
    hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
    (totalBound : Nat)
    (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (leafBound : Nat)
    (hGammaCard :
      ((valuationContext outerVariables valuation).image
        Rewriting.shift).card <= 1) :
    {caseCount : Nat} ->
    caseCount <= totalBound ->
    hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
        valuation body leafBound caseCount <=
      contextualHybridUniversalBranchesPayloadPolynomial
        ((valuationContext outerVariables valuation).image Rewriting.shift)
        totalBound caseCount body leafBound
  | 0, _ => by
      let Gamma := (valuationContext outerVariables valuation).image
        Rewriting.shift
      have hbase := contextualHybridUniversalBaseAssemblyCost_le
        Gamma totalBound body hGammaCard
      simp only [hybridBranchesUniformStructuralPayloadEnvelope,
        contextualHybridUniversalBranchesPayloadPolynomial]
      dsimp only [Gamma] at hbase ⊢
      omega
  | index + 1, hcaseCount => by
      let Gamma := (valuationContext outerVariables valuation).image
        Rewriting.shift
      let localEnvelope := contextualHybridUniversalLocalPayloadEnvelope
        Gamma totalBound body
      have hinitial :=
        hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
          totalBound outerVariables valuation body leafBound hGammaCard
          (caseCount := index) (by omega)
      have hstep := contextualHybridUniversalStepAssemblyCost_le
        Gamma totalBound index body hGammaCard hcaseCount
      have hpoly :
          (index + 1 + 1) * (leafBound + 3 * localEnvelope) =
            (index + 1) * (leafBound + 3 * localEnvelope) +
              (leafBound + 3 * localEnvelope) := by
        ring
      simp only [hybridBranchesUniformStructuralPayloadEnvelope,
        contextualHybridUniversalBranchesPayloadPolynomial]
      simp only [contextualHybridUniversalBranchesPayloadPolynomial] at hinitial
      dsimp only [Gamma, localEnvelope] at hinitial hstep hpoly ⊢
      rw [hpoly]
      omega

#print axioms contextualHybridUniversalBaseAssemblyCost_le
#print axioms contextualHybridUniversalStepAssemblyCost_le
#print axioms
  hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial

def fixedWidthBitLeafUniformAggregateEnvelope
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  (Finset.range (termValue valuation widthTerm)).sum fun bitIndex =>
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
      indexTerm valueTerm bitIndex

theorem fixedWidthBitLeafUniformStructuralEnvelope_le_aggregate
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex ≤
      fixedWidthBitLeafUniformAggregateEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm := by
  unfold fixedWidthBitLeafUniformAggregateEnvelope
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le
      (fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm
        widthTerm indexTerm valueTerm candidate))
    (Finset.mem_range.mpr hbitIndex)

theorem fixedWidthBitHybridBranches_uniformAggregateLeafBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    HybridBranchesLeafPayloadBound
      (fixedWidthBitLeafUniformAggregateEnvelope valuation tableTerm
        widthTerm indexTerm valueTerm)
      (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
        valueTerm (termValue valuation widthTerm) hbits) := by
  exact fixedWidthBitHybridBranches_leafPayloadBound
    valuation tableTerm widthTerm indexTerm valueTerm
    (termValue valuation widthTerm)
    (fixedWidthBitLeafUniformAggregateEnvelope valuation tableTerm widthTerm
      indexTerm valueTerm)
    hbits
    (fun bitIndex hbitIndex =>
      fixedWidthBitLeafUniformStructuralEnvelope_le_aggregate
        valuation tableTerm widthTerm indexTerm valueTerm bitIndex
        hbitIndex)

def fixedWidthBitBranchesTransparentStructuralEnvelope
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue valuation widthTerm
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    valuation body
    (fixedWidthBitLeafUniformAggregateEnvelope valuation tableTerm widthTerm
      indexTerm valueTerm)
    bound

theorem fixedWidthBitBranchesStructuralPayloadEnvelope_le_transparent
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift widthTerm) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue valuation widthTerm) outerFormula.freeVariables
        (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
          valueTerm (termValue valuation widthTerm) hbits) ≤
      fixedWidthBitBranchesTransparentStructuralEnvelope valuation tableTerm
        widthTerm indexTerm valueTerm := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue valuation widthTerm
  let branches := fixedWidthBitHybridBranches valuation tableTerm widthTerm
    indexTerm valueTerm bound hbits
  have hleaves := fixedWidthBitHybridBranches_uniformAggregateLeafBound
    valuation tableTerm widthTerm indexTerm valueTerm hbits
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (fixedWidthBitLeafUniformAggregateEnvelope valuation tableTerm widthTerm
      indexTerm valueTerm)
    branches hleaves
  simpa only [fixedWidthBitBranchesTransparentStructuralEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

def fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let bound := termValue valuation widthTerm
  contextualHybridUniversalBranchesPayloadPolynomial Gamma bound bound body
    (fixedWidthBitLeafAggregateUniformPayloadBound valuation tableTerm
      widthTerm indexTerm valueTerm)

theorem
    fixedWidthBitBranchesStructuralPayloadEnvelope_le_openIndexPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift widthTerm) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue valuation widthTerm) outerFormula.freeVariables
        (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
          valueTerm (termValue valuation widthTerm) hbits) <=
      fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let bound := termValue valuation widthTerm
  let branches := fixedWidthBitHybridBranches valuation tableTerm widthTerm
    indexTerm valueTerm bound hbits
  let leafBound := fixedWidthBitLeafAggregateUniformPayloadBound valuation
    tableTerm widthTerm indexTerm valueTerm
  have hleaves :=
    fixedWidthBitHybridBranches_aggregateUniformLeafPayloadBound_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth
      hindex hvalue hbits
  have huniform :=
    hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
      bound outerVariables leafBound branches hleaves
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma, outerVariables, outerFormula, body]
    exact fixedWidthUniversalShiftedOuterContext_card_le_one_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm
      htable hwidth hindex hvalue
  have hpolynomial :=
    hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
      bound outerVariables valuation body leafBound hGammaCard
      (caseCount := bound) le_rfl
  have htotal := huniform.trans hpolynomial
  simpa only [fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial,
    body, outerFormula, outerVariables, Gamma, bound, branches,
    leafBound] using htotal

def fixedWidthUniversalTransparentStructuralPayloadEnvelope
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (fixedWidthBitBranchesTransparentStructuralEnvelope valuation tableTerm
      widthTerm indexTerm valueTerm)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift widthTerm) body
    (compileShiftedBoundEqualityPayloadResource valuation outerVariables
      widthTerm)
    branchResource

theorem
    fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthUniversalHybridCertificate valuation tableTerm widthTerm
          indexTerm valueTerm hbits) ≤
      fixedWidthUniversalTransparentStructuralPayloadEnvelope valuation
        tableTerm widthTerm indexTerm valueTerm := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branches := fixedWidthBitHybridBranches valuation tableTerm widthTerm
    indexTerm valueTerm bound hbits
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore := fixedWidthBitBranchesTransparentStructuralEnvelope
    valuation tableTerm widthTerm indexTerm valueTerm
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    valuation outerVariables widthTerm
  have hbranchCore : oldBranchCore ≤ newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body]
    exact fixedWidthBitBranchesStructuralPayloadEnvelope_le_transparent
      valuation tableTerm widthTerm indexTerm valueTerm hbits
  have hbranchResource : oldBranchResource ≤ newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift widthTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [fixedWidthUniversalHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    fixedWidthUniversalTransparentStructuralPayloadEnvelope,
    body, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

def fixedWidthUniversalOpenIndexStructuralPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift widthTerm) body
    (compileShiftedBoundEqualityPayloadPublicPolynomial valuation
      outerVariables widthTerm)
    branchResource

theorem
    fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthUniversalHybridCertificate valuation tableTerm widthTerm
          indexTerm valueTerm hbits) <=
      fixedWidthUniversalOpenIndexStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branches := fixedWidthBitHybridBranches valuation tableTerm widthTerm
    indexTerm valueTerm bound hbits
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore :=
    fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let oldBoundResource := compileShiftedBoundEqualityPayloadResource
    valuation outerVariables widthTerm
  let newBoundResource := compileShiftedBoundEqualityPayloadPublicPolynomial
    valuation outerVariables widthTerm
  have hboundResource : oldBoundResource <= newBoundResource := by
    dsimp only [oldBoundResource, newBoundResource]
    exact compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      valuation outerVariables widthTerm hwidth
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body]
    exact
      fixedWidthBitBranchesStructuralPayloadEnvelope_le_openIndexPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm
        htable hwidth hindex hvalue hbits
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift widthTerm) body
    oldBoundResource oldBranchResource newBoundResource newBranchResource
    hboundResource hbranchResource
  simpa only [fixedWidthUniversalHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    fixedWidthUniversalOpenIndexStructuralPayloadPolynomial,
    body, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    oldBoundResource, newBoundResource] using htotal

def fixedWidthOpenIndexPostWitnessStructuralPayloadEnvelope
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
    (fixedWidthUniversalTransparentStructuralPayloadEnvelope valuation
      tableTerm widthTerm indexTerm valueTerm)
  let middleResource := hybridConjunctionStructuralPayloadEnvelope valuation
    lengthFormula innerFormula
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    innerResource
  hybridConjunctionStructuralPayloadEnvelope valuation guardFormula
    middleFormula
    (fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm)
    middleResource

theorem
    compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_openIndexTransparent
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hwidth : widthTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationPostWitnessHybridCertificate
          valuation tableTerm widthTerm indexTerm valueTerm hentry) ≤
      fixedWidthOpenIndexPostWitnessStructuralPayloadEnvelope valuation
        tableTerm widthTerm indexTerm valueTerm := by
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
    fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_transparent
      valuation tableTerm widthTerm indexTerm valueTerm hentry.2
  have hinner := hybridConjunctionStructuralPayloadBound_le_envelope
    sizeGuardCertificate universalCertificate
    (fixedWidthSizeGuardStructuralPayloadPolynomial
      valuation widthTerm valueTerm)
    (fixedWidthUniversalTransparentStructuralPayloadEnvelope valuation
      tableTerm widthTerm indexTerm valueTerm)
    hsizeGuard huniversal
  have hmiddle := hybridConjunctionStructuralPayloadBound_le_envelope
    lengthCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sizeGuardCertificate universalCertificate)
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    (hybridConjunctionStructuralPayloadEnvelope valuation
      (fixedWidthSizeGuard (Nat.size (termValue valuation valueTerm))
        widthTerm)
      (fixedWidthUniversalFormula tableTerm widthTerm indexTerm valueTerm)
      (fixedWidthSizeGuardStructuralPayloadPolynomial
        valuation widthTerm valueTerm)
      (fixedWidthUniversalTransparentStructuralPayloadEnvelope valuation
        tableTerm widthTerm indexTerm valueTerm))
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
        (fixedWidthUniversalTransparentStructuralPayloadEnvelope valuation
          tableTerm widthTerm indexTerm valueTerm)))
    hguard hmiddle
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          lengthCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            sizeGuardCertificate universalCertificate))) ≤ _
  unfold fixedWidthOpenIndexPostWitnessStructuralPayloadEnvelope
  dsimp only
  exact hpost

def compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadEnvelope
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  hybridExistsWitnessStructuralPayloadEnvelope valuation body size
    (fixedWidthOpenIndexPostWitnessStructuralPayloadEnvelope valuation
      tableTerm widthTerm indexTerm valueTerm)

theorem
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexTransparent
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hwidth : widthTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          tableTerm widthTerm indexTerm valueTerm hentry) ≤
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadEnvelope
        valuation tableTerm widthTerm indexTerm valueTerm := by
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
    compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_openIndexTransparent
      valuation tableTerm widthTerm indexTerm valueTerm hwidth hvalue hentry
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated ≤
      fixedWidthOpenIndexPostWitnessStructuralPayloadEnvelope valuation
        tableTerm widthTerm indexTerm valueTerm := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body size instantiated
    (fixedWidthOpenIndexPostWitnessStructuralPayloadEnvelope valuation
      tableTerm widthTerm indexTerm valueTerm)
    hinstantiated
  simpa only [compactFixedWidthEntryAtValuationExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadEnvelope,
    size, body, postCertificate, instantiated] using hexists

def fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial
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
    (fixedWidthUniversalOpenIndexStructuralPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)
  let middleResource := hybridConjunctionStructuralPayloadEnvelope valuation
    lengthFormula innerFormula
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    innerResource
  hybridConjunctionStructuralPayloadEnvelope valuation guardFormula
    middleFormula
    (fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm)
    middleResource

theorem
    compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationPostWitnessHybridCertificate
          valuation tableTerm widthTerm indexTerm valueTerm hentry) <=
      fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
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
    fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm
      htable hwidth hindex hvalue hentry.2
  have hinner := hybridConjunctionStructuralPayloadBound_le_envelope
    sizeGuardCertificate universalCertificate
    (fixedWidthSizeGuardStructuralPayloadPolynomial
      valuation widthTerm valueTerm)
    (fixedWidthUniversalOpenIndexStructuralPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)
    hsizeGuard huniversal
  have hmiddle := hybridConjunctionStructuralPayloadBound_le_envelope
    lengthCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sizeGuardCertificate universalCertificate)
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    (hybridConjunctionStructuralPayloadEnvelope valuation
      (fixedWidthSizeGuard (Nat.size (termValue valuation valueTerm))
        widthTerm)
      (fixedWidthUniversalFormula tableTerm widthTerm indexTerm valueTerm)
      (fixedWidthSizeGuardStructuralPayloadPolynomial
        valuation widthTerm valueTerm)
      (fixedWidthUniversalOpenIndexStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm))
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
        (fixedWidthUniversalOpenIndexStructuralPayloadPolynomial valuation
          tableTerm widthTerm indexTerm valueTerm)))
    hguard hmiddle
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          lengthCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            sizeGuardCertificate universalCertificate))) <= _
  unfold fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial
  dsimp only
  exact hpost

def compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  hybridExistsWitnessStructuralPayloadEnvelope valuation body size
    (fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)

theorem
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          tableTerm widthTerm indexTerm valueTerm hentry) <=
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm := by
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
    compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm
      htable hwidth hindex hvalue hentry
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated <=
      fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body size instantiated
    (fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)
    hinstantiated
  simpa only [compactFixedWidthEntryAtValuationExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial,
    size, body, postCertificate, instantiated] using hexists

#print axioms
  hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
#print axioms fixedWidthBitHybridBranches_uniformAggregateLeafBound
#print axioms
  fixedWidthBitBranchesStructuralPayloadEnvelope_le_transparent
#print axioms
  fixedWidthBitBranchesStructuralPayloadEnvelope_le_openIndexPolynomial
#print axioms
  fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
#print axioms
  compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_openIndexTransparent
#print axioms
  compactFixedWidthEntryAtValuationPostWitnessHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
#print axioms
  compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexTransparent
#print axioms
  compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
