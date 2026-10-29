import DeriveMapM

/-! Tests of `deriving MapM`: one small type per supported shape, checked on values when this file
compiles, and the shapes it refuses, checked by their errors. -/

namespace DeriveMapM.Test

open DeriveMapM

/-- A plain field, a field that leaves the parameter out, and a constructor without it. -/
inductive Plain (ρ : Type) where
  | one (r : ρ) (n : Nat)
  | none
  deriving MapM, DecidableEq, Repr

#guard (Plain.one 3 7).map (· + 1) = .one 4 7
#guard (Plain.none : Plain Nat).map (· + 1) = .none

/-- The containers with instances in the library. -/
structure Containers (ρ : Type) where
  opt : Option ρ
  arr : Array ρ
  list : List ρ
  label : String
  deriving MapM, DecidableEq, Repr

#guard ({ opt := some 1, arr := #[2, 3], list := [4], label := "x" } : Containers Nat).map (· * 10) =
  { opt := some 10, arr := #[20, 30], list := [40], label := "x" }

/-- Pairs, on either side and nested, and inside a container. -/
inductive Pairs (ρ : Type) where
  | left (p : ρ × String)
  | right (p : String × ρ)
  | both (p : ρ × ρ)
  | nested (ps : Array (ρ × (Bool × ρ)))
  deriving MapM, DecidableEq, Repr

#guard (Pairs.left (1, "a")).map toString = .left ("1", "a")
#guard (Pairs.right ("a", 1)).map toString = .right ("a", "1")
#guard (Pairs.both (1, 2)).map toString = .both ("1", "2")
#guard (Pairs.nested #[(1, (true, 2))]).map toString = .nested #[("1", (true, "2"))]

/-- A type that holds another type that derives `MapM`, inside containers too. -/
structure Outer (ρ : Type) where
  plain : Plain ρ
  plains : Array (Option (Plain ρ))
  deriving MapM, DecidableEq, Repr

#guard ({ plain := .one 1 0, plains := #[some (.one 2 0), none] } : Outer Nat).map (· + 1) =
  { plain := .one 2 0, plains := #[some (.one 3 0), none] }

/-- A proof field, which depends on a field that is not mapped, and a function that leaves the
parameter out. -/
inductive Proofs (ρ : Type) where
  | nonempty (xs : Array Nat) (h : xs ≠ #[]) (r : ρ) (f : Nat → Nat)
  deriving MapM

#guard match (Proofs.nonempty #[1] (by decide) 2 id).map (· + 1) with
  | .nonempty xs _ r f => xs == #[1] && r == 3 && f 5 == 5

/-- A recursive type, the type itself a direct field. -/
inductive Chain (ρ : Type) where
  | nil
  | cons (head : ρ) (tail : Chain ρ)
  deriving MapM, DecidableEq, Repr

#guard (Chain.cons 1 (.cons 2 .nil)).map (· * 2) = .cons 2 (.cons 4 .nil)

/-- Other parameters before the one mapped stay as they are. -/
structure Tagged (τ : Type) (n : Nat) (ρ : Type) where
  tag : τ
  refs : Array ρ
  size : Fin (n + 1)
  deriving MapM, DecidableEq, Repr

#guard ({ tag := "t", refs := #[1], size := 0 } : Tagged String 2 Nat).map (· + 1) =
  { tag := "t", refs := #[2], size := 0 }

/-! `mapM` runs the effects in the order of the fields, and stops at the first failure. -/

/-- A map into `Except` that fails on odd numbers, naming them. -/
def evenOnly (n : Nat) : Except Nat Nat := if n % 2 == 0 then .ok (n / 2) else .error n

#guard ((Pairs.nested #[(2, (true, 4)), (6, (false, 8))]).mapM evenOnly).toOption ==
  some (.nested #[(1, (true, 2)), (3, (false, 4))])
#guard match ({ opt := some 2, arr := #[3, 5], list := [7], label := "" } : Containers Nat).mapM evenOnly with
  | .error n => n == 3
  | .ok _ => false
#guard match (Chain.cons 2 (.cons 5 (.cons 7 .nil))).mapM evenOnly with
  | .error n => n == 5
  | .ok _ => false

/-- The order of the effects, recorded in a state. -/
def record (n : Nat) : StateM (Array Nat) Nat := do
  modify (·.push n)
  pure n

#guard (((Tagged.mk () #[1, 2] 0 : Tagged Unit 0 Nat).mapM record).run #[]).2 == #[1, 2]
#guard ((({ plain := .one 1 0, plains := #[some (.one 2 0), none, some (.one 3 0)] } : Outer Nat).mapM
  record).run #[]).2 == #[1, 2, 3]

/-! The instances: `Functor`, and `MapM` used generically. -/

#guard ((· + 1) <$> Plain.one 1 0) = .one 2 0
#guard (MapM.map (· + 1) (Chain.cons 1 .nil)) = .cons 2 .nil

/-! The `simp` lemmas turn the class's functions into the derived ones, and `simp [T.map]` unfolds a
derived `map`. -/

example (g : Nat → Nat) (x : Outer Nat) : MapM.map g x = x.map g := by simp
example (g : Nat → Nat) (x : Containers Nat) :
    (x.map g).arr = x.arr.map g ∧ (x.map g).label = x.label := by
  simp [Containers.map]
example (g : Nat → Nat) (r : Nat) (n : Nat) : (Plain.one r n).map g = .one (g r) n := by
  simp [Plain.map]

/-! Instances among the parameters and the fields. -/

/-- A type function whose `MapM` instance needs an instance on its other parameter. -/
structure Assoc (κ : Type) (ρ : Type) where
  pairs : Array (κ × ρ)
  deriving BEq

instance {κ : Type} [BEq κ] : MapM (Assoc κ) where
  map g a := ⟨a.pairs.map fun (k, r) => (k, g r)⟩
  mapM g a := do return ⟨← a.pairs.mapM fun (k, r) => do return (k, ← g r)⟩

/-- An instance parameter before the one mapped, which the derived functions bind as an instance. -/
structure Wrap (F : Type → Type) [MapM F] (ρ : Type) where
  xs : F ρ
  deriving MapM

#guard ((⟨[1, 2]⟩ : Wrap List Nat).map (· + 1)).xs == [2, 3]

/-- An instance parameter that the field's instance rests on. -/
structure Keyed (κ : Type) [BEq κ] (ρ : Type) where
  entries : Assoc κ ρ
  deriving MapM

#guard ((⟨⟨#[("a", 1)]⟩⟩ : Keyed String Nat).map (· + 1)).entries == ⟨#[("a", 2)]⟩

/-- An instance field that the field's instance rests on, in an inductive type and a structure. -/
inductive WithInst (κ : Type) (ρ : Type) where
  | mk [inst : BEq κ] (entries : Assoc κ ρ)
  deriving MapM

#guard match (WithInst.mk ⟨#[("a", 1)]⟩ : WithInst String Nat).map (· + 1) with
  | @WithInst.mk _ _ _ entries => entries.pairs == #[("a", 2)]

structure WithInstS (κ : Type) (ρ : Type) where
  [inst : BEq κ]
  entries : Assoc κ ρ
  deriving MapM

#guard ((WithInstS.mk ⟨#[("a", 1)]⟩ : WithInstS String Nat).map (· + 1)).entries.pairs == #[("a", 2)]

/-! The shapes `deriving MapM` refuses. -/

/--
error: deriving MapM: the field k of Arrow.f: the parameter appears under a function arrow
-/
#guard_msgs in
inductive Arrow (ρ : Type) where
  | f (k : Nat → ρ)
  deriving MapM

/--
error: deriving MapM: the field m of NotLast.mk: the parameter is an argument of Except ρ Nat other than its last
-/
#guard_msgs in
structure NotLast (ρ : Type) where
  m : Except ρ Nat
  deriving MapM

/--
error: deriving MapM: the field t of NoInstance.mk: Thunk ρ has no instance of MapM (Thunk): derive MapM for it or write one
-/
#guard_msgs in
structure NoInstance (ρ : Type) where
  t : Thunk ρ
  deriving MapM

/--
error: deriving MapM: Tree is a nested inductive type, which is not supported
-/
#guard_msgs in
inductive Tree (ρ : Type) where
  | node (r : ρ) (children : Array (Tree ρ))
  deriving MapM

/--
error: deriving MapM: the last parameter of NotAType is not of type Type
-/
#guard_msgs in
structure NotAType (n : Nat) where
  fin : Fin n
  deriving MapM

/--
error: deriving MapM: the last parameter of Polymorphic is not of type Type
-/
#guard_msgs in
structure Polymorphic.{u} (ρ : Type u) where
  r : ρ
  deriving MapM

/--
error: deriving MapM: Big applied to its parameters is of type Type 1, not Type
-/
#guard_msgs in
structure Big (ρ : Type) where
  r : ρ
  t : Type
  deriving MapM

/--
error: deriving MapM: the field h of Mentions.mk: a proposition that mentions the parameter
-/
#guard_msgs in
structure Mentions (ρ : Type) where
  n : Nat
  h : n = ([] : List ρ).length
  deriving MapM

/--
error: deriving MapM: FieldInstance applied to its parameters is of type Type 1, not Type
-/
#guard_msgs in
structure FieldInstance (F : Type → Type) (ρ : Type) where
  inst : MapM F
  xs : F ρ
  deriving MapM

/--
error: deriving MapM: Clash already declares DeriveMapM.Test.Clash.map
-/
#guard_msgs in
structure Clash (ρ : Type) where
  map : ρ
  deriving MapM

/--
error: deriving MapM: ClassClash already declares DeriveMapM.Test.ClassClash.map_class
-/
#guard_msgs in
structure ClassClash (ρ : Type) where
  map_class : ρ
  deriving MapM

/--
error: deriving MapM: Hidden is private, which is not supported
-/
#guard_msgs in
private structure Hidden (ρ : Type) where
  r : ρ
  deriving MapM

/--
error: deriving MapM: the field h of Dependent.mk: its type depends on a field that is mapped
-/
#guard_msgs in
structure Dependent (ρ : Type) where
  xs : Array ρ
  h : xs.size > 0
  deriving MapM


/-! The example of the README. -/

namespace Readme

inductive Ref (ρ : Type) where
  | record (id : ρ)
  | candidate (asked : ρ) (label : String)
  deriving MapM, LawfulMapM, DecidableEq, Repr

structure Edge (ρ : Type) where
  source : ρ
  targets : Array (Ref ρ)
  weights : List (ρ × Nat)
  note : Option String
  deriving MapM, LawfulMapM, DecidableEq, Repr

def resolve (n : Nat) : Except String String := if n < 10 then .ok s!"#{n}" else .error s!"no record {n}"

#guard ({ source := 1, targets := #[.record 2], weights := [(3, 7)], note := none } : Edge Nat).map toString ==
  { source := "1", targets := #[.record "2"], weights := [("3", 7)], note := none }
#guard match ({ source := 1, targets := #[.candidate 12 "a"], weights := [], note := none } : Edge Nat).mapM
    resolve with
  | .error e => e == "no record 12"
  | .ok _ => false

end Readme

/-! `deriving LawfulMapM` proves the laws, for the shapes above that hold the parameter, and derives
`MapM` first where the type does not. -/

namespace Lawful

inductive Plain (ρ : Type) where
  | one (r : ρ) (n : Nat)
  | none
  deriving MapM, LawfulMapM

structure Containers (ρ : Type) where
  opt : Option ρ
  arr : Array ρ
  list : List ρ
  label : String
  deriving MapM, LawfulMapM

inductive Pairs (ρ : Type) where
  | left (p : ρ × String)
  | right (p : String × ρ)
  | both (p : ρ × ρ)
  | nested (ps : Array (ρ × (Bool × ρ)))
  deriving MapM, LawfulMapM

structure Outer (ρ : Type) where
  plain : Plain ρ
  plains : Array (Option (Plain ρ))
  pairs : List (Pairs ρ)
  deriving MapM, LawfulMapM

inductive Proofs (ρ : Type) where
  | nonempty (xs : Array Nat) (h : xs ≠ #[]) (r : ρ) (f : Nat → Nat)
  deriving MapM, LawfulMapM

inductive Chain (ρ : Type) where
  | nil
  | cons (head : ρ) (tail : Chain ρ)
  deriving MapM, LawfulMapM

structure Tagged (τ : Type) (n : Nat) (ρ : Type) where
  tag : τ
  refs : Array (Chain ρ)
  size : Fin (n + 1)
  deriving MapM, LawfulMapM

/-- An empty type maps trivially. -/
inductive Empty' (ρ : Type) where
  deriving MapM, LawfulMapM

/--
error: deriving LawfulMapM: Twice does not derive MapM: write `deriving MapM, LawfulMapM`
-/
#guard_msgs in
inductive Twice (ρ : Type) where
  | one (r : ρ)
  deriving LawfulMapM, MapM

/-- A proof field over fields that are not mapped, which the proofs of the laws leave alone. -/
structure Clamped (ρ : Type) where
  n : Nat
  m : Nat
  h : n = min n m
  r : ρ
  deriving MapM, LawfulMapM

/-- The same in a recursive inductive type. -/
inductive Bounded (ρ : Type) where
  | nil
  | cons (n m : Nat) (h : n = min n m) (r : ρ) (rest : Bounded ρ)
  deriving MapM, LawfulMapM

/-- A type function with its `MapM` and `LawfulMapM` instances written by hand. -/
structure Box (α : Type) where
  val : α

instance : MapM Box where
  map g b := ⟨g b.val⟩
  mapM g b := do return ⟨← g b.val⟩

instance : LawfulMapM Box where
  map_id _ := rfl
  map_map _ _ _ := rfl
  mapM_id _ _ := rfl

/--
error: deriving LawfulMapM: Box does not derive MapM: write `deriving MapM, LawfulMapM`
-/
#guard_msgs in
deriving instance LawfulMapM for Box

/-- The derived laws use the laws of an instance written by hand. -/
structure Boxed (ρ : Type) where
  boxes : Array (Box ρ)
  box : Box ρ
  deriving MapM, LawfulMapM

/-- A type whose field holds the parameter in a type without the laws. -/
structure Unlawful (ρ : Type) where
  plain : Plain ρ
  deriving MapM

/--
error: deriving LawfulMapM: the field u of NeedsLaws.mk holds Unlawful, which has no LawfulMapM instance: derive LawfulMapM for it first
-/
#guard_msgs in
structure NeedsLaws (ρ : Type) where
  u : Array (Unlawful ρ)
  deriving MapM, LawfulMapM

example (x : Outer Nat) : x.map (fun a => a) = x := Outer.map_id x
example (g : Nat → String) (h : String → Nat) (x : Tagged Unit 3 Nat) :
    (x.map g).map h = x.map fun a => h (g a) := Tagged.map_map g h x
example (g : Nat → String) (x : Chain Nat) : x.mapM (m := Id) (fun a => pure (g a)) = pure (x.map g) :=
  Chain.mapM_id g x
example (x : Pairs Nat) : MapM.map (fun a => a) x = x := LawfulMapM.map_id x

end Lawful

end DeriveMapM.Test
