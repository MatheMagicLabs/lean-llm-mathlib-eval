/-
Exakte Abhängigkeiten einer Lean-Bibliothek (für den Gesetzestest, H2 und Anheftung).

  lake env lean --run Extract.lean <ausgabe.tsv> [Wurzelmodul (Mathlib)] [Modulpräfix (Mathlib)]

Je Zeile: Name TAB Modul TAB Art TAB benutzte Konstanten (aus Typ und Wert, nur solche aus Modulen mit
dem Präfix, ohne interne Hilfskonstanten), durch Leerzeichen getrennt.
-/
import Lean
open Lean

def hilfsname (n : Name) : Bool :=
  n.isInternal || n.components.any fun c =>
    match c with
    | .str _ s => s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_" ||
                  s.startsWith "_" || s == "sizeOf_spec" || s.startsWith "injEq" || s == "noConfusionType" ||
                  s == "noConfusion" || s == "recOn" || s == "casesOn" || s == "below" || s == "brecOn" ||
                  s == "binductionOn" || s == "ibelow"
    | _ => false

def art : ConstantInfo → String
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "ax"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def main (args : List String) : IO UInt32 := do
  let aus := args.getD 0 "abhaengigkeiten.tsv"
  let wurzel := (args.getD 1 "Mathlib").toName
  let praefix := args.getD 2 "Mathlib"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := wurzel }] {} (trustLevel := 1024)
  let mods := env.header.moduleNames
  let modul (n : Name) : Option Name := (env.getModuleIdxFor? n).bind fun i => mods[i.toNat]?
  let drin (n : Name) : Bool :=
    match modul n with
    | some m => m.toString.startsWith praefix && !hilfsname n
    | none => false
  let h ← IO.FS.Handle.mk aus .write
  let mut zeilen : Nat := 0
  let mut kanten : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    if drin n then
      let deps := ci.getUsedConstantsAsSet.toList.filter fun d => d != n && drin d
      let m := (modul n).getD Name.anonymous
      h.putStrLn s!"{n}\t{m}\t{art ci}\t{" ".intercalate (deps.map toString)}"
      zeilen := zeilen + 1
      kanten := kanten + deps.length
  h.flush
  IO.println s!"{zeilen} Deklarationen, {kanten} Kanten -> {aus}"
  return 0
