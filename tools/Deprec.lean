/-
Veraltete (deprecated) Konstanten einer Lean-Bibliothek, für den Mechanismus-Test.

  lake env lean --run Deprec.lean <ausgabe.tsv> [Wurzelmodul (Mathlib)] [Modulpräfix (Mathlib)]

Je Zeile: Name TAB Modul TAB neuer Name (oder -) TAB seit (oder -).
-/
import Lean
open Lean

def main (args : List String) : IO UInt32 := do
  let aus := args.getD 0 "veraltet.tsv"
  let wurzel := (args.getD 1 "Mathlib").toName
  let praefix := args.getD 2 "Mathlib"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := wurzel }] {} (trustLevel := 1024)
  let mods := env.header.moduleNames
  let modul (n : Name) : Option Name := (env.getModuleIdxFor? n).bind fun i => mods[i.toNat]?
  let h ← IO.FS.Handle.mk aus .write
  let mut zeilen : Nat := 0
  let mut gesamt : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    match modul n with
    | some m =>
      if m.toString.startsWith praefix then
        gesamt := gesamt + 1
        match Linter.deprecatedAttr.getParam? env n with
        | some e =>
          let neu := match e.newName? with | some x => x.toString | none => "-"
          let seit := e.since?.getD "-"
          h.putStrLn s!"{n}\t{m}\t{neu}\t{seit}"
          zeilen := zeilen + 1
        | none => pure ()
    | none => pure ()
  h.flush
  IO.println s!"{zeilen} veraltete von {gesamt} Konstanten -> {aus}"
  return 0
