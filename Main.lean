import Dungeon.Tui

/-- `dungeon [seed]`. Without a seed, the clock picks one. -/
def main (args : List String) : IO Unit := do
  let seed ← match args with
    | s :: _ => match s.toNat? with
      | some n => pure n
      | none => throw (IO.userError s!"not a seed: {s}")
    | [] => do
      let ms ← IO.monoMsNow
      pure (ms % 1000000)
  Crawl.Tui.run seed
