module

public import DeriveMapM.Basic
public import DeriveMapM.Handler

@[expose] public section

/-!
# DeriveMapM

`deriving MapM` writes `map` and `mapM` for an inductive type or a structure over its last
parameter, which must be of type `Type`; `deriving LawfulMapM` after it proves that they obey the
functor laws.  `MapM` and `LawfulMapM` are classes this package defines (`DeriveMapM.Basic`), so
open them before a `deriving` clause that names them:

```lean
import DeriveMapM
open DeriveMapM (MapM LawfulMapM)

structure Edge (ρ : Type) where
  source : ρ
  targets : Array ρ
  label : String
  deriving MapM, LawfulMapM

#eval ({ source := 1, targets := #[2, 3], label := "e" } : Edge Nat).map toString
#eval ({ source := 1, targets := #[2, 3], label := "e" } : Edge Nat).mapM fun n =>
  if n < 3 then some n else none
```

It defines `Edge.map`, `Edge.mapM`, the instances `MapM Edge` and `Functor Edge`, and `simp`
lemmas from the class's functions to the derived ones.  `DeriveMapM.Basic` holds the classes and the
instances for `Option`, `List` and `Array`; `DeriveMapM.Handler` the handlers, whose module doc lists
the shapes they map and those they refuse.  It depends on Lean core alone.
-/
