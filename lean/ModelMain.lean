import Intx.Model.MulmodFold
set_option warningAsError true
/-!
# The differential test of the model

Reads the lines `x y m r` of hexadecimal numbers, `r` the result of the C++ `mulmod(x, y, m)`, and
checks that the model gives `r` and that `r` is `x * y % m`, on both platform paths (the x86-64
`div` instruction and the portable reciprocal). See `scripts/difftest.sh`.
-/

open Intx

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def parseHex? (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.foldl (fun acc c => do pure (16 * (← acc) + (← hexDigit? c))) (some 0)

def ofNat256 (n : Nat) : U256 := Vector.ofFn fun i => UInt64.ofNat (n / 2 ^ (64 * i.val))

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut count := 0
  let mut failures := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    match (line.splitOn " ").mapM parseHex? with
    | some [x, y, m, r] =>
      count := count + 1
      for div_wide_x86 in [true, false] do
        let P : Model.Platform := ⟨div_wide_x86⟩
        let got := (Model.mulmod P (ofNat256 x) (ofNat256 y) (ofNat256 m)).map (val ·.toList)
        if got != some r || r != x * y % m then
          failures := failures + 1
          IO.eprintln s!"mismatch (div_wide_x86 {div_wide_x86}): {line}: model {got}, x * y % m = {x * y % m}"
    | _ =>
      IO.eprintln s!"bad line: {line}"
      return 2
  IO.println s!"{count} vectors, {failures} mismatches"
  return if failures == 0 && count > 0 then 0 else 1
