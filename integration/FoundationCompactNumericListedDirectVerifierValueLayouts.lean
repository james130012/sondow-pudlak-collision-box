import integration.FoundationCompactNumericListedDirectParserStateLayout
import integration.FoundationCompactNumericListedTaskMachine
import integration.FoundationCompactNumericListedDirectNatListBoundaryRigidity

/-!
# Direct layouts for verifier stack values

The central verifier stores natural-number lists and child results in its
state tableau.  This module gives both values an exact layout in one public
additive token table and constructs the canonical witnesses.  These are the
typed correctness lemmas used by the later purely numeric state-row formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierValueLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec

def CompactAdditiveNatListDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (values : List Nat) : Prop :=
  ∃ boundaryTable,
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start values.length finish boundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      boundaryTable values ∧
    Nat.size boundaryTable ≤ (values.length + 1) * tokenCount

theorem compactAdditiveNatListDirectLayout_canonical
    (frontTokens : List Nat) (values : List Nat)
    (backTokens : List Nat) :
    let valueTokens := compactAdditiveEncode values
    let tokens := frontTokens ++ valueTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + valueTokens.length
    CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish values := by
  rcases compactAdditiveNatListElementLayouts_canonical
      frontTokens values backTokens with
    ⟨hlayout, hrows, hsize⟩
  exact ⟨_, hlayout, hrows, hsize⟩

theorem CompactAdditiveNatListDirectLayout.toSlice
    {tokenTable width tokenCount start finish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish values) :
    CompactAdditiveNatListSlice
      tokenTable width tokenCount start values.length finish := by
  rcases hlayout with ⟨boundaryTable, hstructure, hrows, _hsize⟩
  have hunit :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows hrows
  have hfinish :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      hstructure hunit
  rcases hstructure with
    ⟨bodyStart, hbodyStart, hheader, _hboundaries⟩
  refine ⟨bodyStart, hbodyStart, hheader, ?_⟩
  have hbody : bodyStart = start + 1 := hheader.1.2.1
  omega

def CompactAdditiveNatListListDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (values : List (List Nat)) : Prop :=
  ∃ boundaryTable,
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start values.length finish boundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      boundaryTable values ∧
    Nat.size boundaryTable ≤ (values.length + 1) * tokenCount

theorem compactAdditiveNatListListDirectLayout_canonical
    (frontTokens : List Nat) (values : List (List Nat))
    (backTokens : List Nat) :
    let valueTokens := compactAdditiveEncode values
    let tokens := frontTokens ++ valueTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + valueTokens.length
    CompactAdditiveNatListListDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish values := by
  rcases compactAdditiveStructuredListElementLayouts_canonical
      CompactAdditiveNatListDirectLayout
      compactAdditiveNatListDirectLayout_canonical
      frontTokens values backTokens with
    ⟨hlayout, hrows, hsize⟩
  exact ⟨_, hlayout, hrows, hsize⟩

def CompactNumericChildResultDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (value : CompactNumericChildResult) : Prop :=
  ∃ gammaFinish gammaBoundaryTable boolValue,
    CompactAdditiveProductSplit tokenCount start gammaFinish finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start value.1.length gammaFinish
      gammaBoundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      gammaBoundaryTable value.1 ∧
    boolValue = compactAdditiveBoolTag value.2 ∧
    CompactAdditiveBoolSlice
      tokenTable width tokenCount gammaFinish boolValue finish ∧
    Nat.size gammaBoundaryTable ≤ (value.1.length + 1) * tokenCount

theorem compactNumericChildResultDirectLayout_canonical
    (frontTokens : List Nat) (value : CompactNumericChildResult)
    (backTokens : List Nat) :
    let valueTokens := compactAdditiveEncode value
    let tokens := frontTokens ++ valueTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + valueTokens.length
    CompactNumericChildResultDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish value := by
  let gamma := value.1
  let result := value.2
  let valueTokens := compactAdditiveEncode value
  let tokens := frontTokens ++ valueTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let gammaFinish := start + (compactAdditiveEncode gamma).length
  let finish := start + valueTokens.length
  let afterGamma := frontTokens ++ compactAdditiveEncode gamma
  have hvalueTokens : valueTokens =
      compactAdditiveEncode gamma ++ compactAdditiveEncode result := by
    change compactAdditiveEncode value = _
    rw [show value = (gamma, result) by rfl]
    exact compactAdditiveEncode_prod (gamma, result)
  have hcommonTokens : tokens =
      frontTokens ++ compactAdditiveEncode gamma ++
        compactAdditiveEncode result ++ backTokens := by
    rw [show tokens = frontTokens ++ valueTokens ++ backTokens by rfl]
    rw [hvalueTokens]
    simp [List.append_assoc]
  have hgammaFull :
      frontTokens ++ compactAdditiveEncode gamma ++
          (compactAdditiveEncode result ++ backTokens) = tokens := by
    simpa [List.append_assoc] using hcommonTokens.symm
  have hresultFull :
      afterGamma ++ compactAdditiveEncode result ++ backTokens = tokens := by
    simpa [afterGamma, List.append_assoc] using hcommonTokens.symm
  have hproductRaw := compactAdditiveProductSplit_canonical
    frontTokens gamma result backTokens
  rcases compactAdditiveStructuredListElementLayouts_canonical
      CompactAdditiveNatListDirectLayout
      compactAdditiveNatListDirectLayout_canonical
      frontTokens gamma (compactAdditiveEncode result ++ backTokens) with
    ⟨hgammaLayout, hgammaRows, hgammaSize⟩
  have hresultRaw := compactAdditiveBoolSlice_canonical
    afterGamma result backTokens
  dsimp only at hproductRaw hgammaLayout hgammaRows hgammaSize hresultRaw
  rw [hgammaFull] at hgammaLayout hgammaRows hgammaSize
  rw [hresultFull] at hresultRaw
  have hafterGamma : afterGamma.length = gammaFinish := by
    simp [afterGamma, gammaFinish, start]
  have hfinish : finish = gammaFinish +
      (compactAdditiveEncode result).length := by
    dsimp only [finish, gammaFinish]
    rw [hvalueTokens]
    simp only [List.length_append]
    omega
  have hresultLength : (compactAdditiveEncode result).length = 1 := by
    cases result <;> rfl
  have hproduct : CompactAdditiveProductSplit
      tokens.length start gammaFinish finish := by
    simpa only [start, gammaFinish, hfinish] using hproductRaw
  have hgammaLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start gamma.length gammaFinish
      (compactAdditiveStructuredListElementBoundaryTable
        tokens.length (start + 1) gamma) := by
    simpa only [width, gammaFinish] using hgammaLayout
  have hgammaRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length
      (compactAdditiveStructuredListElementBoundaryTable
        tokens.length (start + 1) gamma) gamma := by
    simpa only [width] using hgammaRows
  have hresult' : CompactAdditiveBoolSlice
      (compactFixedWidthTableCode width tokens)
      width tokens.length gammaFinish
      (compactAdditiveBoolTag result) finish := by
    simpa only [width, hafterGamma, hfinish, hresultLength] using hresultRaw
  have hgammaSize' : Nat.size
      (compactAdditiveStructuredListElementBoundaryTable
        tokens.length (start + 1) gamma) ≤
      (gamma.length + 1) * tokens.length := hgammaSize
  exact ⟨gammaFinish,
    compactAdditiveStructuredListElementBoundaryTable
      tokens.length (start + 1) gamma,
    compactAdditiveBoolTag result,
    hproduct, hgammaLayout', hgammaRows', rfl, hresult', hgammaSize'⟩

#print axioms compactAdditiveNatListDirectLayout_canonical
#print axioms CompactAdditiveNatListDirectLayout.toSlice
#print axioms compactAdditiveNatListListDirectLayout_canonical
#print axioms compactNumericChildResultDirectLayout_canonical

end FoundationCompactNumericListedDirectVerifierValueLayouts
