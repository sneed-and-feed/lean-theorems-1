import Lean

open Lean

/-- Recursively collect all constants reachable from an expression. -/
partial def collectUsedConstants (env : Environment) (c : Name) (visited : NameSet) : NameSet :=
  if visited.contains c then visited
  else
    let visited := visited.insert c
    match env.find? c with
    | none => visited
    | some info =>
      let constsInType := info.type.getUsedConstants
      let constsInVal := match info.value? with
        | some v => v.getUsedConstants
        | none => #[]
      let allConsts := constsInType ++ constsInVal
      allConsts.foldl (fun s next => collectUsedConstants env next s) visited

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let compJsonStr ← IO.FS.readFile "comparator.json"
  let json ← match Json.parse compJsonStr with
    | Except.ok j => pure j
    | Except.error e => throw (IO.userError s!"Failed to parse comparator.json: {e}")
  
  let thmNames ← match json.getObjVal? "theorem_names" with
    | Except.ok (Json.arr arr) => arr.mapM fun j => match j.getStr? with
      | Except.ok s => pure (s.toName)
      | Except.error e => throw (IO.userError s!"Invalid theorem name string: {e}")
    | _ => throw (IO.userError "Missing or invalid theorem_names array in comparator.json")

  let envC ← importModules #[{ module := `Challenge }] {}
  let envS ← importModules #[{ module := `Solution }] {}
  
  let mut hasMismatch := false
  let mut allUsed : NameSet := {}

  -- 1. Check all target theorems for type equality
  for thmName in thmNames do
    match envC.find? thmName with
    | none =>
      IO.eprintln s!"[BLOCKING FAIL] Declaration '{thmName}' not found in Challenge module!"
      hasMismatch := true
    | some infoC =>
      match envS.find? thmName with
      | none =>
        IO.eprintln s!"[BLOCKING FAIL] Declaration '{thmName}' not found in Solution module!"
        hasMismatch := true
      | some infoS =>
        if infoC.type == infoS.type then
          IO.println s!"[PASS] AST Expression Match: '{thmName}'"
        else
          IO.eprintln s!"[BLOCKING FAIL] AST Mismatch for '{thmName}':"
          IO.eprintln s!"  Challenge AST: {infoC.type}"
          IO.eprintln s!"  Solution AST:  {infoS.type}"
          hasMismatch := true
        -- Collect constants used in target theorem's type
        for c in infoC.type.getUsedConstants do
          allUsed := collectUsedConstants envC c allUsed

  -- 2. Transitive constant-graph walk for non-target constants (AP-20 & AP-32)
  IO.println s!"==> Walking {allUsed.size} transitive constant dependencies..."
  let targetSet : NameSet := thmNames.foldl (fun s n => s.insert n) {}
  let mut constMismatchCount := 0

  for c in allUsed do
    if !targetSet.contains c then
      match envC.find? c, envS.find? c with
      | some infoC, some infoS =>
        let typeEq := infoC.type == infoS.type
        let valEq := match infoC, infoS with
          | .thmInfo tC, .thmInfo tS => tC.value == tS.value
          | .defnInfo dC, .defnInfo dS => dC.value == dS.value
          | _, _ => true
        if !typeEq || !valEq then
          IO.eprintln s!"[BLOCKING FAIL] Transitive Constant Mismatch for '{c}':"
          IO.eprintln s!"  typeMatch: {typeEq}, valMatch: {valEq}"
          hasMismatch := true
          constMismatchCount := constMismatchCount + 1
      | some _, none =>
        IO.eprintln s!"[BLOCKING FAIL] Transitive constant '{c}' missing in Solution!"
        hasMismatch := true
        constMismatchCount := constMismatchCount + 1
      | none, some _ =>
        IO.eprintln s!"[BLOCKING FAIL] Transitive constant '{c}' missing in Challenge!"
        hasMismatch := true
        constMismatchCount := constMismatchCount + 1
      | none, none => pure ()

  if hasMismatch then
    IO.eprintln s!"[FAIL] Comparator pre-flight verification failed with {constMismatchCount} constant mismatches."
    return 1
  else
    IO.println s!"[PASS] All {thmNames.size} targets and {allUsed.size} transitive constants match 100%."
    return 0