import integration.SondowProjectBigNCleanSubmissionRoute
import Lean
import Lean.Data.Json.FromToJson
import Lean.Elab.BuiltinCommand
import Lean.Meta.Basic
import Lean.Message

open Lean Elab Term Meta Std

set_option linter.deprecated false

/-
Lean 4.31 does not expose imported theorem proof bodies through `value?`.
The upstream lean-graph extractor therefore sees no references for imported
theorems in this project.  This project-local extractor keeps the lean-graph
JSON schema, but collects constants from declaration types and visible
definition bodies, then filters to the project namespace so the graph remains
readable.
-/

def keepProjectName (n : Name) : Bool :=
  let s := toString n
  s.startsWith "SondowMainCheckedCodeBridge" ||
  s == "is_rational" ||
  s == "euler_mascheroni" ||
  s == "Eq" ||
  s == "Not" ||
  s == "And" ||
  s == "Max.max" ||
  s == "Nat" ||
  s == "Real"

def getConstTypeLabel (n : Name) : TermElabM String := do
  let constInfo ← getConstInfo n
  return match constInfo with
    | ConstantInfo.defnInfo _ => "Definition"
    | ConstantInfo.thmInfo _  => "Theorem"
    | ConstantInfo.axiomInfo _ => "Axiom"
    | _ => "Other"

def getTypeStrOf (n : Name) : TermElabM String := do
  let inf ← getConstInfo n
  let dat ← ppExpr inf.toConstantVal.type
  return s!"{dat}"

def getTypeAndBodyConsts (n : Name) : TermElabM (Array Name) := do
  let info ← getConstInfo n
  let typeConsts := info.toConstantVal.type.getUsedConstants
  let bodyConsts := match info.value? with
    | some b => b.getUsedConstants
    | none => #[]
  let all := (HashSet.ofArray (typeConsts ++ bodyConsts)).toArray
  all.filterM fun m => do
    if !keepProjectName m then
      return false
    try
      let _ ← getConstInfo m
      pure true
    catch _ =>
      pure false

structure BFSState where
  g : HashMap Name (List Name)
  outerLayer : List Name

def getGraph (names : List Name) (depth : Nat) :
    TermElabM (List (Name × List Name)) := do
  let state ← (List.range depth).foldlM
    (fun (state : BFSState) (_ : Nat) => do
      let g := state.g
      let newNodes ← state.outerLayer.mapM fun name => do
        let consts ← try getTypeAndBodyConsts name catch | _ => pure #[]
        pure (name, consts)
      let g := newNodes.foldl (fun m p => m.insert p.fst p.snd.toList) g
      let newOuterLayer := newNodes.foldl
        (fun (set : HashSet Name) (node : Name × Array Name) =>
          set.insertMany node.snd)
        HashSet.emptyWithCapacity
      let newOuterLayer := newOuterLayer.toList.filter (fun n => !(g.contains n))
      return BFSState.mk g newOuterLayer)
    (BFSState.mk HashMap.emptyWithCapacity names)
  return state.g.toList

def writeJsonToFile (filePath : String) (json : Json) : IO Unit := do
  IO.FS.withFile filePath IO.FS.Mode.write fun handle =>
    handle.putStr (toString json)

def pairToJson (pair : Name × List Name) : TermElabM (Option Json) := do
  let nameStr := toString pair.fst
  let constCategoryStr ← try getConstTypeLabel pair.fst catch | _ => return none
  let constTypeStr ← try getTypeStrOf pair.fst catch | _ => pure ""
  let refs := pair.snd.map (fun n => Json.str (toString n)) |>.toArray
  return Json.mkObj [
    ("name", Json.str nameStr),
    ("constCategory", Json.str constCategoryStr),
    ("constType", Json.str constTypeStr),
    ("references", Json.arr refs)
  ]

def serializeList (l : List (Name × List Name)) : TermElabM Json := do
  let res ← l.filterMapM pairToJson
  return Json.arr res.toArray

def serializeAndWriteConstTypeGraph
    (name : Name) (depth : Nat) (filePath : String) : TermElabM Unit := do
  let g ← getGraph [name] depth
  let js ← serializeList g
  writeJsonToFile filePath js

#eval serializeAndWriteConstTypeGraph
  `SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute.cleanUpperProvider_submissionRoute
  3
  "paper/lean_graph/cleanUpperProvider_submissionRoute.project_type.depth3.json"

#eval serializeAndWriteConstTypeGraph
  `SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute.cleanComputedBigN_eq_tailGapMax
  3
  "paper/lean_graph/cleanComputedBigN_eq_tailGapMax.project_type.depth3.json"

#eval serializeAndWriteConstTypeGraph
  `SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute.cleanProvider_not_rational
  3
  "paper/lean_graph/cleanProvider_not_rational.project_type.depth3.json"
