# DeriveMapM

A deriving handler for Lean 4 that writes `map`, `mapM`, a `Functor` instance and the functor laws for a structure or an inductive type, over its last type parameter.  It is the counterpart of Haskell's `deriving (Functor, Traversable)`, and of the handlers in Mathlib, for projects that do not depend on Mathlib.  It needs Lean core alone: no Mathlib, no Batteries.

The handler writes syntax, as core's own deriving handlers do, and writes the definitions so that `simp [T.map]` unfolds them down to `Array.map`, `Option.map` and the other types' own `map`.

```lean
import DeriveMapM
open DeriveMapM (MapM LawfulMapM)

inductive Ref (ρ : Type) where
  | record (id : ρ)
  | candidate (asked : ρ) (label : String)
  deriving MapM, LawfulMapM, Repr

structure Edge (ρ : Type) where
  source : ρ
  targets : Array (Ref ρ)
  weights : List (ρ × Nat)
  note : Option String
  deriving MapM, LawfulMapM, Repr

-- pure
#eval ({ source := 1, targets := #[.record 2], weights := [(3, 7)], note := none } : Edge Nat).map toString
-- in a monad, failing at the first id that does not resolve
def resolve (n : Nat) : Except String String := if n < 10 then .ok s!"#{n}" else .error s!"no record {n}"
#eval ({ source := 1, targets := #[.candidate 12 "a"], weights := [], note := none } : Edge Nat).mapM resolve
```

## Using it

Add it to your `lakefile.toml` (the URL is a placeholder until the repository is published):

```toml
[[require]]
name = "DeriveMapM"
git = "https://example.invalid/derive-mapm"
rev = "main"
```

or, in a `lakefile.lean`, `require DeriveMapM from git "https://example.invalid/derive-mapm" @ "main"`.  Then `import DeriveMapM`.  Write `open DeriveMapM (MapM LawfulMapM)` before a `deriving` clause that names them, or write `deriving DeriveMapM.MapM`.

The package is built and tested with Lean v4.35.0 (`lean-toolchain`); `lake test` runs the tests in `DeriveMapM/Test.lean`.  It has not been tried with other versions.

## What it writes

For a type `T … ρ` whose last parameter `ρ : Type` is the one mapped, `deriving MapM` defines, in `T`'s namespace:

- `T.map (g : α → β) : T … α → T … β`, a structural map (a `match` on the constructors of an inductive type; the projections of a structure);
- `T.mapM [Monad m] (g : α → m β) : T … α → m (T … β)`, which runs the effects of `g` in the order of the fields, the elements of an array or a list from first to last;
- the instances `MapM (T …)` and `Functor (T …)`;
- the `simp` lemmas `T.map_class` and `T.mapM_class`, which turn `MapM.map` and `MapM.mapM` at `T` into `T.map` and `T.mapM`, so that `simp [T.map]` unfolds a derived map down to `Array.map`, `Option.map` and the other types' own `map`.

Calls such as `x.map g` and `x.mapM g` resolve to them by dot notation.  Parameters before `ρ` stay as they are; an instance parameter among them (`structure Wrap (F : Type → Type) [MapM F] (ρ : Type)`) stays an instance, so a field's `MapM` instance may rest on it, or on a constructor field of class type (`[inst : BEq κ]`).

`deriving LawfulMapM`, after `deriving MapM` (`deriving MapM, LawfulMapM`), proves, as `simp` lemmas, `T.map_id` (`x.map (fun a => a) = x`), `T.map_map` (`(x.map g).map h = x.map (fun a => h (g a))`) and `T.mapM_id` (`mapM` in `Id` of a pure function is `map`), and gives the instance `LawfulMapM (T …)`.  The proofs go by structural recursion and `simp` on each constructor, leaving the constructor's proof fields out of the simp set, and need the laws of the types the fields hold: `Option`, `List`, `Array`, those that derive `LawfulMapM`, and instances of `LawfulMapM` written by hand; the handler refuses a field that holds the parameter in a type without a `LawfulMapM` instance.

## Supported shapes

A field is mapped by its type:

- `ρ`: by `g`;
- `F τ` where `F : Type → Type` does not mention `ρ` and has a `MapM` instance (`Option`, `List`, `Array`, any type that derives `MapM`, or an instance written by hand): by `MapM.map`, mapping each `τ` inside the same way, so `Array (Option (Ref ρ))` works;
- `α × β`: each side that mentions `ρ`, nested pairs included;
- `T … ρ` itself as a field (not inside another type): by a recursive call, which Lean checks as structural recursion;
- a type that does not mention `ρ`, functions and proofs included: left as it is.

Several constructors, constructors without arguments, and fields whose types depend on earlier fields that are not mapped (a proof that a list is non-empty, say) are fine.

## Refused shapes

The handler refuses, with an error that names the field and the reason:

- `ρ` under a function arrow (`Nat → ρ`);
- `ρ` as an argument other than the last (`Except ρ Nat`);
- a type without a `MapM` instance (`Thunk ρ`);
- a field whose type depends on a field that is mapped (`h : xs.size > 0` after `xs : Array ρ`), and a proposition that mentions `ρ` in any other way;
- the type being defined inside another type (a nested inductive type such as `node : Array (Tree ρ) → Tree ρ`), mutual families, indexed families, a last parameter that is not of type `Type`, and a type `T … ρ` that is not itself of type `Type` (a structure with a field `t : Type` or `inst : MapM F`, a proposition);
- a type that already declares one of the names the handler writes (a field named `map` or `map_class`, say);
- a `private` type;
- `deriving LawfulMapM` on a type that does not derive `MapM` first, a hand-written instance included.

## Limits

- One parameter is mapped, the last.  Universe-polymorphic parameters (`ρ : Type u`) are not supported: the class is over `Type → Type`.
- No `Traversable` (core Lean has no such class): `mapM` asks for a `Monad`, not an `Applicative`.
- `private` types are refused rather than given private derived declarations.
- Not tried with Lean's module system (files that begin with `module`).
- Nested inductive types are refused rather than handled by well-founded recursion.

## Prior art

Mathlib's [`Mathlib/Tactic/DeriveTraversable.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/DeriveTraversable.lean) derives `Functor`, `Traversable` and their lawful versions, building the definitions as expressions and mapping nested fields through `Functor` instances.  It depends on Mathlib's `Traversable` hierarchy.  DeriveMapM covers the same ground for users who do not depend on Mathlib, generates syntax rather than expressions (as core's own deriving handlers do), maps through pairs, and writes the definitions so that `simp [T.map]` unfolds them.
