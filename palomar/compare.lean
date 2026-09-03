import Lean

open Lean

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
  
  if hasMismatch then
    return 1
  else
    return 0