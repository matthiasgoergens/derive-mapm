# DeriveMapM

A deriving handler for Lean 4 that writes `map` and `mapM` for a structure or an inductive type, over its last type parameter, and can prove that they obey the functor laws.  It is in the spirit of Haskell's `deriving (Functor, Traversable)`, for projects that do not depend on Mathlib: it needs Lean core alone, no Mathlib and no Batteries.

`MapM` and `LawfulMapM` are classes that this package defines (in `DeriveMapM.Basic`), not part of Lean core.  `MapM f` says how to map the values of type `α` inside an `f α`, purely (`map`) or in a monad (`mapM`).  `LawfulMapM f` adds the laws.  `deriving MapM` gives a type a `MapM` instance and a `Functor` instance; the laws come only with `deriving LawfulMapM`, which goes after it.

```lean
import DeriveMapM
open DeriveMapM (MapM LawfulMapM)

inductive Tree (ρ : Type) where
  | leaf (value : ρ)
  | node (left right : Tree ρ)
  deriving MapM, LawfulMapM, Repr

structure Entry (ρ : Type) where
  key : ρ
  trees : Array (Tree ρ)
  counts : List (ρ × Nat)
  note : Option String
  deriving MapM, LawfulMapM, Repr

def entry : Entry Nat :=
  { key := 1, trees := #[.node (.leaf 2) (.leaf 3)], counts := [(4, 7)], note := none }

-- Pure: apply a function to every `Nat` that the `Entry` holds (the `7` is a different `Nat`, not a `ρ`).
#eval entry.map toString
-- { key := "1", trees := #[Tree.node (Tree.leaf "2") (Tree.leaf "3")], counts := [("4", 7)], note := none }

-- In a monad: look every value up, stopping at the first one that is missing.
def lookup (table : List (Nat × String)) (n : Nat) : Except String String :=
  match table.lookup n with
  | some s => .ok s
  | none => .error s!"no entry {n}"

#eval entry.mapM (lookup [(1, "one"), (2, "two"), (3, "three"), (4, "four")])
-- Except.ok { key := "one", trees := #[Tree.node (Tree.leaf "two") (Tree.leaf "three")], counts := [("four", 7)], note := none }
#eval entry.mapM (lookup [(1, "one"), (2, "two")])
-- Except.error "no entry 3"
```

## Using it

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "DeriveMapM"
git = "https://github.com/matthiasgoergens/derive-mapm"
rev = "v0.2.0"
```

or, in a `lakefile.lean`, `require DeriveMapM from git "https://github.com/matthiasgoergens/derive-mapm" @ "v0.2.0"`.  Then `import DeriveMapM` (`public import DeriveMapM` in a module).  Write `open DeriveMapM (MapM LawfulMapM)` before a `deriving` clause that names them, or write `deriving DeriveMapM.MapM`.

The package pins Lean v4.35.0 (`lean-toolchain`) and needs at least v4.32.0: it has been built, and its tests run, with v4.32.0, v4.33.0, v4.34.1, v4.35.0 and v4.36.0-rc1.  v4.31.0 rejects the handler's code, and in v4.26.0 the `module` keyword is still experimental.  `lake test` builds the tests in `DeriveMapM/Test.lean`: they are checks that run while the file compiles (values compared with `#guard`, and the error of each refused shape compared with `#guard_msgs`), so a build without errors is a pass.

## Modules

Since v0.2.0 the package is written in Lean's module system: every file starts with `module`, and the handler is `meta` code, which runs while a `deriving` clause elaborates.  A module that derives `MapM` needs only `public import DeriveMapM`; the handler comes with it.  The definitions and lemmas it writes are declared where the `deriving` clause is, with that place's visibility: in an `@[expose] public section` other modules can unfold `T.map`, in a plain `public section` they get its type and the `simp` lemmas only.  A structure with a `private` field is mapped by a `match`, since a module's exposed definitions may not name a private projection.

A file that is not a module imports the package as before: it loads every part of each module it imports, so it sees and can unfold everything, as with v0.1.0.

## What it writes

For a type `T … ρ` whose last parameter `ρ : Type` is the one mapped, `deriving MapM` defines, in `T`'s namespace:

- `T.map (g : α → β) : T … α → T … β`: a `match` on the constructors for an inductive type, and the constructor applied to the projections for a structure;
- `T.mapM [Monad m] (g : α → m β) : T … α → m (T … β)`, which runs the effects of `g` in the order of the fields, and the elements of an array or a list from first to last;
- the instances `MapM (T …)` and `Functor (T …)`;
- the `simp` lemmas `T.map_class` and `T.mapM_class`, which turn `MapM.map` and `MapM.mapM` at `T` into `T.map` and `T.mapM`.

`simp [T.map]` then unfolds a derived map down to `Array.map`, `Option.map` and the other types' own `map`.  Calls such as `x.map g` and `x.mapM g` resolve by dot notation.  Parameters before `ρ` stay as they are.  An instance parameter among them (`structure Wrap (F : Type → Type) [MapM F] (ρ : Type)`) stays an instance, so a field's `MapM` instance may rest on it.  The same holds for a constructor field of class type, as in this tiny example, where mapping `Keyed` needs `BEq κ` for the hand-written `MapM (Assoc κ)`:

```lean
structure Assoc (κ ρ : Type) where
  pairs : Array (κ × ρ)

instance {κ : Type} [BEq κ] : MapM (Assoc κ) where
  map g a := ⟨a.pairs.map fun (k, r) => (k, g r)⟩
  mapM g a := do return ⟨← a.pairs.mapM fun (k, r) => do return (k, ← g r)⟩

inductive Keyed (κ ρ : Type) where
  | mk [inst : BEq κ] (entries : Assoc κ ρ)
  deriving MapM
```

`deriving LawfulMapM`, after `deriving MapM` (write `deriving MapM, LawfulMapM`), proves three lemmas and gives the instance `LawfulMapM (T …)`.  The lemmas are `T.map_id` (`x.map (fun a => a) = x`), `T.map_map` (`(x.map g).map h = x.map (fun a => h (g a))`) and `T.mapM_id` (`mapM` in `Id` of a pure function is `map`), all marked `@[simp]`.  The proofs go constructor by constructor, with `simp` and the same lemmas for the fields that hold the type itself.  They do not use the fields that are proofs.  They need the laws of the types that the fields hold: `Option`, `List`, `Array`, types that derive `LawfulMapM`, and `LawfulMapM` instances written by hand.  The handler refuses a field that holds the parameter in a type without a `LawfulMapM` instance.

## Supported shapes

A field is mapped according to its type:

- `ρ`: by `g`;
- `F τ`, where `F : Type → Type` does not mention `ρ` and has a `MapM` instance (`Option`, `List`, `Array`, any type that derives `MapM`, or an instance written by hand): by `MapM.map`, mapping each `τ` inside in the same way, so `Array (Option (Tree ρ))` works;
- `α × β`: each side that mentions `ρ`, nested pairs included;
- `T … ρ` itself as a field (not inside another type): by a recursive call that Lean accepts without a termination argument;
- a type that does not mention `ρ`, functions and proofs included: left as it is.

Abbreviations (`abbrev`, or other reducible definitions) in a field's type are unfolded first.  Several constructors, constructors without arguments, and fields whose types depend on earlier fields that are not mapped (a proof that a list is non-empty, say) are fine.  A structure that `extends` another works when the parent derives `MapM` too (and `LawfulMapM`, for the laws), because the parent is a field.

## Refused shapes

Every refusal is an error at the `deriving` clause with a message that gives the reason.  Errors about one field name the field and its constructor (a field without a name is called an unnamed field); errors about the whole type name the type.

Refused, naming the field:

- `ρ` under a function arrow (`Nat → ρ`);
- `ρ` as an argument other than the last (`Except ρ Nat`);
- a type without a `MapM` instance (`Thunk ρ`), including a parent structure that does not derive `MapM`;
- a field whose type depends on a field that is mapped (`h : xs.size > 0` after `xs : Array ρ`), and a proposition that mentions `ρ` in any other way;
- `deriving LawfulMapM` on a field that holds the parameter in a type without a `LawfulMapM` instance, including a type parameter such as `F` in `structure Wrap (F : Type → Type) [MapM F] (ρ : Type)`: its laws cannot be assumed, so `deriving MapM` works for `Wrap` and `deriving LawfulMapM` does not.

Refused, naming the type:

- a nested inductive type, one that holds itself inside another type (`node : Array (Tree ρ) → Tree ρ`), mutual families and indexed families;
- a last parameter that is not of type `Type` (`ρ : Type u`, say), and a type `T … ρ` that is not itself of type `Type` (a structure with a field `t : Type` or `inst : MapM F`, a proposition);
- a type that already declares one of the names the handler writes (a field named `map` or `map_class`, say);
- a `private` type;
- `deriving LawfulMapM` on a type that does not derive `MapM` first, a hand-written instance included.

## Limits

- One parameter is mapped, the last.  Universe-polymorphic parameters (`ρ : Type u`) are not supported: the class is over `Type → Type`.
- It is Functor-like, not Traversable: core Lean has no `Traversable` class, and `mapM` asks for a `Monad`, not an `Applicative`.
- `private` types are refused rather than given private derived declarations.
- Nested inductive types are refused rather than handled by well-founded recursion.

## Prior art

Mathlib's [`Mathlib/Tactic/DeriveTraversable.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/DeriveTraversable.lean) derives `Functor`, `Traversable` (Haskell's class for a `mapM` over any `Applicative`) and their lawful versions, building the definitions as expressions and mapping nested fields through `Functor` instances.  It depends on Mathlib's `Traversable` hierarchy.  DeriveMapM covers the map and the monadic map for users who do not depend on Mathlib, generates syntax rather than expressions (as core's own deriving handlers do), and maps through pairs.

## Licence

Apache-2.0; see `LICENSE`.
