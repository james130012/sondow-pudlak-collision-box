import integration.FoundationCompactNumericListedDirectTrace
import integration.FoundationCompactAdditiveTokenCodec

/-!
# Additive code for the complete compact verifier trace

This module instantiates the flat additive token codec at every intermediate
state type in `CompactNumericListedDirectTrace`.  The staging instances keep
typeclass search from unfolding the entire nested witness in one step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTraceCode

open FoundationCompactAdditiveTokenCodec
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactPackedTokenStreamDirectTrace
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactSequentValueDirectTrace
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedRootFieldsDirectTrace
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace

local instance compactNatListPrimcodable : Primcodable (List Nat) :=
  @Primcodable.list Nat inferInstance

local instance compactNumericSequentValuePrimcodable :
    Primcodable CompactNumericSequentValue :=
  @Primcodable.list (List Nat) compactNatListPrimcodable

local instance compactNumericChildResultPrimcodable :
    Primcodable CompactNumericChildResult :=
  @Primcodable.prod CompactNumericSequentValue Bool
    compactNumericSequentValuePrimcodable inferInstance

local instance compactSyntaxTaskAdditiveCodec :
    CompactAdditiveTokenCodec CompactSyntaxTask :=
  inferInstance

local instance compactUnifiedParserStateAdditiveCodec :
    CompactAdditiveTokenCodec CompactUnifiedParserState :=
  inferInstance

local instance binaryNatStreamStateAdditiveCodec :
    CompactAdditiveTokenCodec BinaryNatStreamState :=
  inferInstance

local instance compactFormulaTokenValuesResultAdditiveCodec :
    CompactAdditiveTokenCodec CompactFormulaTokenValuesResult :=
  inferInstance

local instance compactFormulaValuesNestedDirectTraceAdditiveCodec :
    CompactAdditiveTokenCodec CompactFormulaValuesNestedDirectTrace :=
  inferInstance

local instance compactNumericNodeFieldsAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericNodeFields :=
  inferInstance

local instance compactNumericRootFieldBranchDirectTracePrimcodable :
    Primcodable CompactNumericRootFieldBranchDirectTrace :=
  inferInstance

local instance compactNumericRootFieldBranchDirectTraceAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericRootFieldBranchDirectTrace :=
  inferInstance

local instance compactPackedTokenStreamDirectTraceAdditiveCodec :
    CompactAdditiveTokenCodec CompactPackedTokenStreamDirectTrace :=
  inferInstance

local instance compactNumericVerifierTaskAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericVerifierTask :=
  inferInstance

local instance compactNumericChildResultAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericChildResult :=
  inferInstance

local instance compactNumericVerifierStateAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericVerifierState :=
  inferInstance

local instance compactNumericParserDirectTracesPrimcodable :
    Primcodable CompactNumericParserDirectTraces :=
  inferInstance

local instance compactNumericParserDirectTracesAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericParserDirectTraces :=
  inferInstance

local instance compactNumericParsedDirectTraceDataPrimcodable :
    Primcodable CompactNumericParsedDirectTraceData :=
  inferInstance

local instance compactNumericParsedDirectTraceDataAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericParsedDirectTraceData :=
  inferInstance

local instance compactNumericDirectTraceTailPrimcodable :
    Primcodable CompactNumericDirectTraceTail :=
  inferInstance

local instance compactNumericDirectTraceTailAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericDirectTraceTail :=
  inferInstance

local instance compactNumericListedDirectTraceAdditiveCodec :
    CompactAdditiveTokenCodec CompactNumericListedDirectTrace :=
  inferInstance

def compactNumericListedDirectTraceTokens
    (trace : CompactNumericListedDirectTrace) : List Nat :=
  compactAdditiveEncode trace

/-- Honest structural weight of the complete direct trace token stream. -/
def compactNumericListedDirectTraceWeight
    (trace : CompactNumericListedDirectTrace) : Nat :=
  compactAdditiveTokenWeight
    (compactNumericListedDirectTraceTokens trace)

/-- Audit-facing decomposition of the total trace weight into the twelve
semantic components carried by the public witness. -/
def compactNumericListedDirectTraceComponentWeight
    (trace : CompactNumericListedDirectTrace) : Nat :=
  (compactAdditiveValueWeight
      (compactNumericDirectTraceCertifiedTokens trace) +
    compactAdditiveValueWeight
      (compactNumericDirectTraceCertifiedStreamTrace trace)) +
  ((compactAdditiveValueWeight
      (compactNumericDirectTraceFormulaTokens trace) +
    compactAdditiveValueWeight
      (compactNumericDirectTraceFormulaStreamTrace trace)) +
  ((compactAdditiveValueWeight
      (compactNumericDirectTraceProofParserTrace trace) +
    (compactAdditiveValueWeight
      (compactNumericDirectTraceCertificateParserTrace trace) +
    compactAdditiveValueWeight
      (compactNumericDirectTraceFormulaParserTrace trace))) +
  (compactAdditiveValueWeight (compactNumericDirectTraceParts trace) +
  (compactAdditiveValueWeight (compactNumericDirectTraceRoot trace) +
  (compactAdditiveValueWeight
      (compactNumericDirectTraceRootBranchTrace trace) +
  (compactAdditiveValueWeight
      (compactNumericDirectTraceFormulaValue trace) +
    compactAdditiveValueWeight
      (compactNumericDirectTraceStates trace)))))))

theorem compactNumericListedDirectTraceWeight_eq_components
    (trace : CompactNumericListedDirectTrace) :
    compactNumericListedDirectTraceWeight trace =
      compactNumericListedDirectTraceComponentWeight trace := by
  change compactAdditiveValueWeight trace = _
  rw [compactAdditiveValueWeight_prod trace]
  rw [compactAdditiveValueWeight_prod trace.1]
  rw [compactAdditiveValueWeight_prod trace.2]
  rw [compactAdditiveValueWeight_prod trace.2.1]
  rw [compactAdditiveValueWeight_prod trace.2.2]
  rw [compactAdditiveValueWeight_prod trace.2.2.1]
  rw [compactAdditiveValueWeight_prod trace.2.2.1.2]
  rw [compactAdditiveValueWeight_prod trace.2.2.2]
  rw [compactAdditiveValueWeight_prod trace.2.2.2.2]
  rw [compactAdditiveValueWeight_prod trace.2.2.2.2.2]
  rw [compactAdditiveValueWeight_prod trace.2.2.2.2.2.2]
  unfold compactNumericListedDirectTraceComponentWeight
  rfl

/-- Honest additive weight of one central verifier configuration. -/
def compactNumericVerifierStateWeight
    (state : CompactNumericVerifierState) : Nat :=
  compactAdditiveValueWeight state

/-- The five audit-facing components of one verifier configuration. -/
def compactNumericVerifierStateComponentWeight
    (state : CompactNumericVerifierState) : Nat :=
  ((compactAdditiveValueWeight state.1.1.1 +
      compactAdditiveValueWeight state.1.1.2) +
    (compactAdditiveValueWeight state.1.2.1 +
      compactAdditiveValueWeight state.1.2.2)) +
    compactAdditiveValueWeight state.2

theorem compactNumericVerifierStateWeight_eq_components
    (state : CompactNumericVerifierState) :
    compactNumericVerifierStateWeight state =
      compactNumericVerifierStateComponentWeight state := by
  change compactAdditiveValueWeight state = _
  rw [compactAdditiveValueWeight_prod state]
  rw [compactAdditiveValueWeight_prod state.1]
  rw [compactAdditiveValueWeight_prod state.1.1]
  rw [compactAdditiveValueWeight_prod state.1.2]
  rfl

/-- Explicit row budget once stream, task, and child-result invariants have
been supplied. -/
def compactNumericVerifierStateBudget
    (streamBound itemCount taskBound childBound : Nat) : Nat :=
  ((streamBound + streamBound) +
    ((Nat.size itemCount + 1 + itemCount * taskBound) +
      (Nat.size itemCount + 1 + itemCount * childBound))) + 4

theorem compactNumericVerifierStateWeight_le_budget
    (state : CompactNumericVerifierState)
    (streamBound itemCount taskBound childBound : Nat)
    (hproof : compactAdditiveValueWeight state.1.1.1 <= streamBound)
    (hcertificate : compactAdditiveValueWeight state.1.1.2 <= streamBound)
    (htaskLength : state.1.2.1.length <= itemCount)
    (hvalueLength : state.1.2.2.length <= itemCount)
    (htasks : ∀ task ∈ state.1.2.1,
      compactAdditiveValueWeight task <= taskBound)
    (hvalues : ∀ value ∈ state.1.2.2,
      compactAdditiveValueWeight value <= childBound) :
    compactNumericVerifierStateWeight state <=
      compactNumericVerifierStateBudget
        streamBound itemCount taskBound childBound := by
  have htaskRaw := compactAdditiveValueWeight_list_le
    state.1.2.1 taskBound htasks
  have htaskSize := Nat.size_le_size htaskLength
  have htaskProduct := Nat.mul_le_mul_right taskBound htaskLength
  have htask : compactAdditiveValueWeight state.1.2.1 <=
      Nat.size itemCount + 1 + itemCount * taskBound := by
    omega
  have hvalueRaw := compactAdditiveValueWeight_list_le
    state.1.2.2 childBound hvalues
  have hvalueSize := Nat.size_le_size hvalueLength
  have hvalueProduct := Nat.mul_le_mul_right childBound hvalueLength
  have hvalue : compactAdditiveValueWeight state.1.2.2 <=
      Nat.size itemCount + 1 + itemCount * childBound := by
    omega
  have hstatus := compactAdditiveValueWeight_option_bool_le state.2
  rw [compactNumericVerifierStateWeight_eq_components]
  unfold compactNumericVerifierStateComponentWeight
  unfold compactNumericVerifierStateBudget
  omega

/-- Honest weight of the complete central verifier tableau. -/
def compactNumericVerifierStateTableWeight
    (states : List CompactNumericVerifierState) : Nat :=
  compactAdditiveValueWeight states

theorem compactNumericVerifierStateTableWeight_le_of_rows
    (states : List CompactNumericVerifierState) (rowBound : Nat)
    (hrows : ∀ state ∈ states,
      compactNumericVerifierStateWeight state <= rowBound) :
    compactNumericVerifierStateTableWeight states <=
      Nat.size states.length + 1 + states.length * rowBound := by
  unfold compactNumericVerifierStateTableWeight
  apply compactAdditiveValueWeight_list_le
  intro state hstate
  exact hrows state hstate

theorem compactNumericVerifierLocalTrace_tableWeight_le
    (fuel : Nat) (start : CompactNumericVerifierState)
    (states : List CompactNumericVerifierState) (rowBound : Nat)
    (hvalid : CompactNumericVerifierLocalTraceValid fuel start states)
    (hrows : ∀ state ∈ states,
      compactNumericVerifierStateWeight state <= rowBound) :
    compactNumericVerifierStateTableWeight states <=
      Nat.size (fuel + 1) + 1 + (fuel + 1) * rowBound := by
  have htable :=
    compactNumericVerifierStateTableWeight_le_of_rows
      states rowBound hrows
  simpa [hvalid.1] using htable

def compactNumericListedDirectTraceTokenDecode
    (tokens : List Nat) :
    Option (CompactNumericListedDirectTrace × List Nat) :=
  compactAdditiveDecode tokens

theorem compactNumericListedDirectTraceTokenDecode_encode_append
    (trace : CompactNumericListedDirectTrace) (suffix : List Nat) :
    compactNumericListedDirectTraceTokenDecode
        (compactNumericListedDirectTraceTokens trace ++ suffix) =
      some (trace, suffix) :=
  compactAdditiveDecode_encode_append trace suffix

theorem compactNumericListedDirectTraceTokens_primrec :
    Primrec compactNumericListedDirectTraceTokens :=
  compactAdditiveEncode_primrec

theorem compactNumericListedDirectTraceTokenDecode_primrec :
    Primrec compactNumericListedDirectTraceTokenDecode :=
  compactAdditiveDecode_primrec

def compactNumericListedDirectTraceCode
    (trace : CompactNumericListedDirectTrace) : Nat :=
  compactAdditivePackedCode
    (compactNumericListedDirectTraceTokens trace)

def compactNumericListedDirectTraceDecodeFinish
    (parsed : CompactNumericListedDirectTrace × List Nat) :
    Option CompactNumericListedDirectTrace :=
  if parsed.2 = [] then some parsed.1 else none

def compactNumericListedDirectTraceCodeDecode
    (code : Nat) : Option CompactNumericListedDirectTrace :=
  (compactPackedTokenStream code).bind fun tokens =>
    (compactNumericListedDirectTraceTokenDecode tokens).bind
      compactNumericListedDirectTraceDecodeFinish

theorem compactNumericListedDirectTraceCode_primrec :
    Primrec compactNumericListedDirectTraceCode :=
  compactAdditivePackedCode_primrec.comp
    compactNumericListedDirectTraceTokens_primrec

theorem compactNumericListedDirectTraceDecodeFinish_primrec :
    Primrec compactNumericListedDirectTraceDecodeFinish := by
  have hempty : PrimrecPred (fun parsed :
      CompactNumericListedDirectTrace × List Nat => parsed.2 = []) :=
    Primrec.eq.comp Primrec.snd (Primrec.const [])
  have hsome : Primrec (fun parsed :
      CompactNumericListedDirectTrace × List Nat => some parsed.1) :=
    Primrec.option_some.comp Primrec.fst
  exact
    (Primrec.ite hempty hsome (Primrec.const none)).of_eq fun parsed => by
      simp [compactNumericListedDirectTraceDecodeFinish]

theorem compactNumericListedDirectTraceCodeDecode_primrec :
    Primrec compactNumericListedDirectTraceCodeDecode := by
  have htokens : Primrec (fun code : Nat =>
      compactPackedTokenStream code) :=
    compactPackedTokenStream_primrec
  have hfinished : Primrec₂
      (fun (_state : Nat × List Nat)
          (parsed : CompactNumericListedDirectTrace × List Nat) =>
        compactNumericListedDirectTraceDecodeFinish parsed) :=
    compactNumericListedDirectTraceDecodeFinish_primrec.comp₂
      Primrec₂.right
  have hdecodeTokens : Primrec₂
      (fun (code : Nat) (tokens : List Nat) =>
        (compactNumericListedDirectTraceTokenDecode tokens).bind
          compactNumericListedDirectTraceDecodeFinish) := by
    apply Primrec₂.mk
    exact Primrec.option_bind
      (compactNumericListedDirectTraceTokenDecode_primrec.comp
        Primrec.snd)
      hfinished
  exact
    (Primrec.option_bind htokens hdecodeTokens).of_eq fun code => by
      rfl

theorem compactNumericListedDirectTraceCodeDecode_code
    (trace : CompactNumericListedDirectTrace) :
    compactNumericListedDirectTraceCodeDecode
        (compactNumericListedDirectTraceCode trace) = some trace := by
  unfold compactNumericListedDirectTraceCodeDecode
  unfold compactNumericListedDirectTraceCode
  rw [compactPackedTokenStream_additivePackedCode]
  simp only [Option.bind_some]
  rw [show compactNumericListedDirectTraceTokenDecode
      (compactNumericListedDirectTraceTokens trace) =
        some (trace, []) by
      simpa using
        compactNumericListedDirectTraceTokenDecode_encode_append trace []]
  rfl

theorem compactNumericListedDirectTraceCode_injective :
    Function.Injective compactNumericListedDirectTraceCode := by
  intro left right hcode
  have hdecoded := congrArg compactNumericListedDirectTraceCodeDecode hcode
  simpa [compactNumericListedDirectTraceCodeDecode_code] using hdecoded

theorem compactNumericListedDirectTraceCode_size
    (trace : CompactNumericListedDirectTrace) :
    Nat.size (compactNumericListedDirectTraceCode trace) =
      compactAdditiveTokenBitLength
          (compactNumericListedDirectTraceTokens trace) + 1 := by
  simp [compactNumericListedDirectTraceCode]

theorem compactNumericListedDirectTraceCode_size_eq_weight
    (trace : CompactNumericListedDirectTrace) :
    Nat.size (compactNumericListedDirectTraceCode trace) =
      2 * compactNumericListedDirectTraceWeight trace + 1 := by
  rw [compactNumericListedDirectTraceCode_size]
  rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
  rfl

#print axioms compactNumericListedDirectTraceTokenDecode_encode_append
#print axioms compactNumericListedDirectTraceTokens_primrec
#print axioms compactNumericListedDirectTraceTokenDecode_primrec
#print axioms compactNumericListedDirectTraceCode_primrec
#print axioms compactNumericListedDirectTraceCodeDecode_primrec
#print axioms compactNumericListedDirectTraceCodeDecode_code
#print axioms compactNumericListedDirectTraceCode_injective
#print axioms compactNumericListedDirectTraceCode_size
#print axioms compactNumericListedDirectTraceWeight_eq_components
#print axioms compactNumericListedDirectTraceCode_size_eq_weight
#print axioms compactNumericVerifierStateWeight_eq_components
#print axioms compactNumericVerifierStateWeight_le_budget
#print axioms compactNumericVerifierStateTableWeight_le_of_rows
#print axioms compactNumericVerifierLocalTrace_tableWeight_le

end FoundationCompactNumericListedDirectTraceCode
