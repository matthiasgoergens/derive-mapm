import DeriveMapM.Basic
import DeriveMapM.Handler

/-!
# DeriveMapM

`deriving MapM` writes `map` and `mapM` for an inductive type or a structure over its last
parameter, which must be of type `Type`:

```lean
import DeriveMapM
open DeriveMapM

structure Edge (ρ : Type) where
  source : ρ
  targets : Array ρ
  label : String
  deriving MapM

#eval ({ source := 1, targets := #[2, 3], label := "e" } : Edge Nat).map toString
#eval ({ source := 1, targets := #[2, 3], label := "e" } : Edge Nat).mapM fun n =>
  if n < 3 then some n else none
```

It defines `Edge.map`, `Edge.mapM`, the instances `MapM Edge` and `Functor Edge`, and `simp`
lemmas from the class's functions to the derived ones.  `DeriveMapM.Basic` holds the class and its
instances for `Option`, `List` and `Array`; `DeriveMapM.Handler` the handler, whose module doc lists
the shapes it maps and those it refuses.  It depends on Lean core alone.
-/
