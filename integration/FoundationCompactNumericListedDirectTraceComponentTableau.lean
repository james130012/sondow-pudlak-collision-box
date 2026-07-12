import integration.FoundationCompactNumericListedDirectAdditiveCodecGraph
import integration.FoundationCompactNumericListedDirectTraceCode
import Mathlib.Tactic.FinCases

/-!
# Twelve-component boundary tableau for the complete direct trace

The additive trace codec is a concatenation of twelve semantic component
streams.  This module exposes their thirteen boundaries in one polynomial-size
table.  Internal component grammars remain separate later obligations.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTraceComponentTableau

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericRootFieldBranchDirectTracePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParserDirectTracesPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParsedDirectTraceDataPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericDirectTraceTailPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.binaryNatStreamStateAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactFormulaTokenValuesResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactFormulaValuesNestedDirectTraceAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericRootFieldBranchDirectTraceAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactPackedTokenStreamDirectTraceAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericParserDirectTracesAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericParsedDirectTraceDataAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericDirectTraceTailAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericListedDirectTraceAdditiveCodec

/-- Every concrete additive codec constructor used by the trace emits at least
one token. -/
class CompactAdditiveNonemptyCodec
    (α : Type*) [Primcodable α] [CompactAdditiveTokenCodec α] : Prop where
  encode_ne_nil : ∀ value : α, compactAdditiveEncode value ≠ []

instance compactNatAdditiveNonemptyCodec :
    CompactAdditiveNonemptyCodec Nat where
  encode_ne_nil _ := by simp

instance compactBoolAdditiveNonemptyCodec :
    CompactAdditiveNonemptyCodec Bool where
  encode_ne_nil value := by
    cases value <;> simp

instance compactOptionAdditiveNonemptyCodec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    CompactAdditiveNonemptyCodec (Option α) where
  encode_ne_nil value := by
    cases value <;> simp

instance compactProdAdditiveNonemptyCodec
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    [CompactAdditiveNonemptyCodec α] :
    CompactAdditiveNonemptyCodec (α × β) where
  encode_ne_nil value := by
    rw [compactAdditiveEncode_prod]
    exact List.append_ne_nil_of_left_ne_nil
      (CompactAdditiveNonemptyCodec.encode_ne_nil value.1) _

instance compactListAdditiveNonemptyCodec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    CompactAdditiveNonemptyCodec (List α) where
  encode_ne_nil values := by
    simp

theorem compactAdditiveEncode_ne_nil
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    [CompactAdditiveNonemptyCodec α] (value : α) :
    compactAdditiveEncode value ≠ [] :=
  CompactAdditiveNonemptyCodec.encode_ne_nil value

/-- The exact audit-facing order of the twelve top-level trace components. -/
def compactNumericListedDirectTraceComponentTokens
    (trace : CompactNumericListedDirectTrace) : List (List Nat) :=
  [compactAdditiveEncode (compactNumericDirectTraceCertifiedTokens trace),
   compactAdditiveEncode
      (compactNumericDirectTraceCertifiedStreamTrace trace),
   compactAdditiveEncode (compactNumericDirectTraceFormulaTokens trace),
   compactAdditiveEncode
      (compactNumericDirectTraceFormulaStreamTrace trace),
   compactAdditiveEncode
      (compactNumericDirectTraceProofParserTrace trace),
   compactAdditiveEncode
      (compactNumericDirectTraceCertificateParserTrace trace),
   compactAdditiveEncode
      (compactNumericDirectTraceFormulaParserTrace trace),
   compactAdditiveEncode (compactNumericDirectTraceParts trace),
   compactAdditiveEncode (compactNumericDirectTraceRoot trace),
   compactAdditiveEncode
      (compactNumericDirectTraceRootBranchTrace trace),
   compactAdditiveEncode (compactNumericDirectTraceFormulaValue trace),
   compactAdditiveEncode (compactNumericDirectTraceStates trace)]

@[simp] theorem compactNumericListedDirectTraceComponentTokens_length
    (trace : CompactNumericListedDirectTrace) :
    (compactNumericListedDirectTraceComponentTokens trace).length = 12 := by
  simp [compactNumericListedDirectTraceComponentTokens]

theorem compactNumericListedDirectTraceComponentTokens_ne_nil
    (trace : CompactNumericListedDirectTrace) :
    ∀ component ∈ compactNumericListedDirectTraceComponentTokens trace,
      component ≠ [] := by
  intro component hcomponent
  simp only [compactNumericListedDirectTraceComponentTokens,
    List.mem_cons, List.not_mem_nil, or_false] at hcomponent
  rcases hcomponent with hcomponent | hcomponent | hcomponent |
      hcomponent | hcomponent | hcomponent | hcomponent | hcomponent |
      hcomponent | hcomponent | hcomponent | hcomponent <;>
    subst component <;> exact compactAdditiveEncode_ne_nil _

theorem compactNumericListedDirectTraceTokens_eq_flatten_components
    (trace : CompactNumericListedDirectTrace) :
    compactNumericListedDirectTraceTokens trace =
      (compactNumericListedDirectTraceComponentTokens trace).flatten := by
  simp [compactNumericListedDirectTraceTokens,
    compactNumericListedDirectTraceComponentTokens,
    compactNumericDirectTraceCertifiedTokens,
    compactNumericDirectTraceCertifiedStreamTrace,
    compactNumericDirectTraceFormulaTokens,
    compactNumericDirectTraceFormulaStreamTrace,
    compactNumericDirectTraceProofParserTrace,
    compactNumericDirectTraceCertificateParserTrace,
    compactNumericDirectTraceFormulaParserTrace,
    compactNumericDirectTraceParts,
    compactNumericDirectTraceRoot,
    compactNumericDirectTraceRootBranchTrace,
    compactNumericDirectTraceFormulaValue,
    compactNumericDirectTraceStates,
    compactAdditiveEncode_prod, List.append_assoc]

/-- Cumulative starts of a list of nonempty token slices. -/
def compactAdditiveComponentBoundaries : List (List Nat) → List Nat
  | [] => [0]
  | component :: components =>
      0 :: (compactAdditiveComponentBoundaries components).map
        (fun cursor => component.length + cursor)

@[simp] theorem compactAdditiveComponentBoundaries_length
    (components : List (List Nat)) :
    (compactAdditiveComponentBoundaries components).length =
      components.length + 1 := by
  induction components with
  | nil => simp [compactAdditiveComponentBoundaries]
  | cons component components ih =>
      simp [compactAdditiveComponentBoundaries, ih]

@[simp] theorem compactAdditiveComponentBoundaries_getI_zero
    (components : List (List Nat)) :
    (compactAdditiveComponentBoundaries components).getI 0 = 0 := by
  cases components <;> rfl

theorem compactAdditiveComponentBoundaries_getI_succ
    (component : List Nat) (components : List (List Nat)) (index : Nat)
    (hindex : index < (compactAdditiveComponentBoundaries components).length) :
    (compactAdditiveComponentBoundaries (component :: components)).getI
        (index + 1) =
      component.length +
        (compactAdditiveComponentBoundaries components).getI index := by
  simp only [compactAdditiveComponentBoundaries]
  rw [List.getI_cons_succ]
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  rw [List.getI_eq_getElem _ hindex]
  simp

theorem compactAdditiveComponentBoundaries_final
    (components : List (List Nat)) :
    (compactAdditiveComponentBoundaries components).getI components.length =
      components.flatten.length := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      change
        (compactAdditiveComponentBoundaries
          (component :: components)).getI (components.length + 1) = _
      rw [compactAdditiveComponentBoundaries_getI_succ
        component components components.length (by simp)]
      simp [ih]

theorem compactAdditiveComponentBoundaries_strict
    (components : List (List Nat))
    (hne : ∀ component ∈ components, component ≠ [])
    (index : Nat) (hindex : index < components.length) :
    (compactAdditiveComponentBoundaries components).getI index <
      (compactAdditiveComponentBoundaries components).getI (index + 1) := by
  induction components generalizing index with
  | nil => simp at hindex
  | cons component components ih =>
      have hcomponent : component ≠ [] := hne component (by simp)
      have hcomponentPos : 0 < component.length :=
        List.length_pos_iff.mpr hcomponent
      cases index with
      | zero =>
          rw [compactAdditiveComponentBoundaries_getI_zero]
          rw [compactAdditiveComponentBoundaries_getI_succ
            component components 0 (by simp)]
          simp [hcomponentPos]
      | succ index =>
          have hindexTail : index < components.length := by
            simpa using hindex
          have htailNonempty :
              ∀ tailComponent ∈ components, tailComponent ≠ [] := by
            intro tailComponent htail
            exact hne tailComponent (by simp [htail])
          rw [compactAdditiveComponentBoundaries_getI_succ
            component components index (by simp; omega)]
          rw [compactAdditiveComponentBoundaries_getI_succ
            component components (index + 1) (by simp; omega)]
          exact Nat.add_lt_add_left
            (ih htailNonempty index hindexTail) component.length

theorem compactAdditiveComponentBoundaries_bounded
    (components : List (List Nat)) :
    ∀ cursor ∈ compactAdditiveComponentBoundaries components,
      cursor ≤ components.flatten.length := by
  induction components with
  | nil => simp [compactAdditiveComponentBoundaries]
  | cons component components ih =>
      intro cursor hcursor
      simp only [compactAdditiveComponentBoundaries,
        List.mem_cons, List.mem_map] at hcursor
      rcases hcursor with rfl | ⟨tailCursor, htailCursor, rfl⟩
      · simp
      · have htailBound := ih tailCursor htailCursor
        simp only [List.flatten_cons, List.length_append]
        omega

def compactNumericListedDirectTraceBoundaryTable
    (trace : CompactNumericListedDirectTrace) : Nat :=
  let components := compactNumericListedDirectTraceComponentTokens trace
  compactFixedWidthTableCode
    (compactNumericListedDirectTraceTokens trace).length
    (compactAdditiveComponentBoundaries components)

theorem compactNumericListedDirectTrace_boundaryTable
    (trace : CompactNumericListedDirectTrace) :
    CompactAdditiveBoundaryTable
      (compactNumericListedDirectTraceTokens trace).length 12 0
      (compactNumericListedDirectTraceTokens trace).length
      (compactNumericListedDirectTraceBoundaryTable trace) := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  have hflatten : components.flatten =
      compactNumericListedDirectTraceTokens trace :=
    (compactNumericListedDirectTraceTokens_eq_flatten_components trace).symm
  have hlength : components.length = 12 :=
    compactNumericListedDirectTraceComponentTokens_length trace
  unfold compactNumericListedDirectTraceBoundaryTable
  dsimp only
  apply compactAdditiveBoundaryTable_of_rows
  · simp
  · exact compactAdditiveComponentBoundaries_getI_zero components
  · simpa [hlength, hflatten] using
      compactAdditiveComponentBoundaries_final components
  · intro cursor hcursor
    simpa [hflatten] using
      compactAdditiveComponentBoundaries_bounded components cursor hcursor
  · intro index hindex
    apply compactAdditiveComponentBoundaries_strict components
    · exact compactNumericListedDirectTraceComponentTokens_ne_nil trace
    · simpa [hlength] using hindex

/-- The packed trace token stream and its twelve top-level component
boundaries, both represented by direct bounded arithmetic graphs. -/
def CompactCanonicalTraceComponentTableau
    (traceCode tokenCount tokenTable offsetTable
      partCount start finish boundaryTable : Nat) : Prop :=
  CompactCanonicalPackedTokenStreamTableau
      traceCode tokenCount tokenTable offsetTable ∧
    CompactAdditiveBoundaryTable
      tokenCount partCount start finish boundaryTable

def compactCanonicalTraceComponentTableauDef : 𝚺₀.Semisentence 8 := .mkSigma
  “traceCode tokenCount tokenTable offsetTable
      partCount start finish boundaryTable.
    !(compactCanonicalPackedTokenStreamTableauDef)
      traceCode tokenCount tokenTable offsetTable ∧
    !(compactAdditiveBoundaryTableDef)
      tokenCount partCount start finish boundaryTable”

@[simp] theorem compactCanonicalTraceComponentTableauDef_spec
    (traceCode tokenCount tokenTable offsetTable
      partCount start finish boundaryTable : Nat) :
    compactCanonicalTraceComponentTableauDef.val.Evalb
        ![traceCode, tokenCount, tokenTable, offsetTable,
          partCount, start, finish, boundaryTable] ↔
      CompactCanonicalTraceComponentTableau
        traceCode tokenCount tokenTable offsetTable
        partCount start finish boundaryTable := by
  have hstream := compactCanonicalPackedTokenStreamTableauDef_spec
    traceCode tokenCount tokenTable offsetTable
  have hboundary := compactAdditiveBoundaryTableDef_spec
    tokenCount partCount start finish boundaryTable
  simp [compactCanonicalTraceComponentTableauDef,
    CompactCanonicalTraceComponentTableau, hstream]
  intro _
  have henv :
      (Semiterm.val
          ![traceCode, tokenCount, tokenTable, offsetTable,
            partCount, start, finish, boundaryTable]
          Empty.elim ∘
        ![(#1 : Semiterm ℒₒᵣ Empty 8), #4, #5, #6, #7]) =
        ![tokenCount, partCount, start, finish, boundaryTable] := by
    funext index
    fin_cases index <;> rfl
  rw [henv]
  exact hboundary

theorem compactCanonicalTraceComponentTableauDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCanonicalTraceComponentTableauDef.val := by
  simp [compactCanonicalTraceComponentTableauDef]

theorem compactCanonicalTraceComponentTableau_canonical
    (trace : CompactNumericListedDirectTrace) :
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    CompactCanonicalTraceComponentTableau
      (compactNumericListedDirectTraceCode trace)
      tokens.length
      (compactFixedWidthTableCode width tokens)
      (compactFixedWidthTableCode width
        (compactBinaryNatTokenOffsets tokens))
      12 0 tokens.length
      (compactNumericListedDirectTraceBoundaryTable trace) := by
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  have hcode : compactNumericListedDirectTraceCode trace =
      compactAdditivePackedCode tokens := by
    rfl
  refine ⟨?_, compactNumericListedDirectTrace_boundaryTable trace⟩
  rw [hcode]
  exact compactCanonicalPackedTokenStreamTableau_canonical tokens

theorem compactNumericListedDirectTraceBoundaryTable_size_le
    (trace : CompactNumericListedDirectTrace) :
    Nat.size (compactNumericListedDirectTraceBoundaryTable trace) ≤
      13 * (compactNumericListedDirectTraceTokens trace).length := by
  unfold compactNumericListedDirectTraceBoundaryTable
  simpa [compactNumericListedDirectTraceComponentTokens_length,
    Nat.mul_comm] using
    compactAdditiveBoundaryTable_code_size_le
      (compactNumericListedDirectTraceTokens trace).length
      (compactAdditiveComponentBoundaries
        (compactNumericListedDirectTraceComponentTokens trace))

#print axioms compactAdditiveEncode_ne_nil
#print axioms compactNumericListedDirectTraceComponentTokens_length
#print axioms compactNumericListedDirectTraceComponentTokens_ne_nil
#print axioms compactNumericListedDirectTraceTokens_eq_flatten_components
#print axioms compactAdditiveComponentBoundaries_final
#print axioms compactAdditiveComponentBoundaries_strict
#print axioms compactAdditiveComponentBoundaries_bounded
#print axioms compactNumericListedDirectTrace_boundaryTable
#print axioms compactCanonicalTraceComponentTableauDef_spec
#print axioms compactCanonicalTraceComponentTableauDef_sigmaZero
#print axioms compactCanonicalTraceComponentTableau_canonical
#print axioms compactNumericListedDirectTraceBoundaryTable_size_le

end FoundationCompactNumericListedDirectTraceComponentTableau
