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

#print axioms compactNumericListedDirectTraceTokenDecode_encode_append
#print axioms compactNumericListedDirectTraceTokens_primrec
#print axioms compactNumericListedDirectTraceTokenDecode_primrec
#print axioms compactNumericListedDirectTraceCode_primrec
#print axioms compactNumericListedDirectTraceCodeDecode_primrec
#print axioms compactNumericListedDirectTraceCodeDecode_code
#print axioms compactNumericListedDirectTraceCode_injective
#print axioms compactNumericListedDirectTraceCode_size

end FoundationCompactNumericListedDirectTraceCode
