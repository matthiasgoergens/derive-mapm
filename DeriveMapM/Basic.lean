module

@[expose] public section

/-!
# The `MapM` class

`MapM f` says how to map the values of type `α` that an `f α` holds, purely (`MapM.map`) or in a
monad (`MapM.mapM`), keeping everything else.  `deriving MapM` (`DeriveMapM.Handler`) writes it for an
inductive type or a structure from its constructors, and uses the instances below, and those of the
other types that derive it, for the fields that hold the parameter inside another type.

The class is smaller than a traversable functor: `mapM` asks only for a `Monad`, and the class states
no laws.  `LawfulMapM` adds the two functor laws for `map` and the agreement of `mapM` at `Id` with
`map`; `deriving LawfulMapM` proves them for a type that derives `MapM` (`deriving MapM, LawfulMapM`).
-/

namespace DeriveMapM

/-- How to map the values of type `α` held by an `f α`: purely, and in a monad, with the effects in
the order the values are held (a structure's fields and a constructor's arguments in their declared
order, an array's or a list's elements from first to last). -/
class MapM (f : Type → Type) where
  /-- The value with each `α` it holds mapped by `g`. -/
  map {α β : Type} (g : α → β) : f α → f β
  /-- The value with each `α` it holds mapped by `g`, in the monad `m`. -/
  mapM {m : Type → Type} [Monad m] {α β : Type} (g : α → m β) : f α → m (f β)

/-- The laws of a `MapM` instance: `map` keeps the value under the identity and composes, and `mapM`
in `Id` is `map`. -/
class LawfulMapM (f : Type → Type) [MapM f] : Prop where
  map_id {α : Type} (x : f α) : MapM.map (fun a => a) x = x
  map_map {α β γ : Type} (g : α → β) (h : β → γ) (x : f α) :
    MapM.map h (MapM.map g x) = MapM.map (fun a => h (g a)) x
  mapM_id {α β : Type} (g : α → β) (x : f α) :
    MapM.mapM (m := Id) (fun a => pure (g a)) x = pure (MapM.map g x)

instance : MapM Option where
  map := Option.map
  mapM g x := x.mapM g

instance : MapM List where
  map := List.map
  mapM g xs := xs.mapM g

instance : MapM Array where
  map := Array.map
  mapM g xs := xs.mapM g

section
variable {α β : Type}

@[simp] theorem map_option (g : α → β) (x : Option α) : MapM.map g x = x.map g := rfl
@[simp] theorem map_list (g : α → β) (xs : List α) : MapM.map g xs = xs.map g := rfl
@[simp] theorem map_array (g : α → β) (xs : Array α) : MapM.map g xs = xs.map g := rfl
@[simp] theorem mapM_option {m : Type → Type} [Monad m] (g : α → m β) (x : Option α) :
    MapM.mapM g x = x.mapM g := rfl
@[simp] theorem mapM_list {m : Type → Type} [Monad m] (g : α → m β) (xs : List α) :
    MapM.mapM g xs = xs.mapM g := rfl
@[simp] theorem mapM_array {m : Type → Type} [Monad m] (g : α → m β) (xs : Array α) :
    MapM.mapM g xs = xs.mapM g := rfl

/-- `Option.mapM` of a pure function is pure (the counterpart of `List.mapM_pure` and
`Array.mapM_pure`). -/
@[simp] theorem option_mapM_pure {m : Type → Type} [Monad m] [LawfulMonad m] (g : α → β)
    (x : Option α) :
    x.mapM (fun a => (pure (g a) : m β)) = pure (x.map g) := by
  cases x <;> simp

end

instance : LawfulMapM Option where
  map_id x := by cases x <;> rfl
  map_map g h x := by cases x <;> rfl
  mapM_id g x := by cases x <;> rfl

instance : LawfulMapM List where
  map_id xs := by simp
  map_map g h xs := by simp [Function.comp_def]
  mapM_id g xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [mapM_list, map_list, List.mapM_cons, List.map_cons] at ih ⊢
      rw [ih]
      rfl

instance : LawfulMapM Array where
  map_id xs := by simp
  map_map g h xs := by simp [Function.comp_def]
  mapM_id g xs := by
    rcases xs with ⟨xs⟩
    have := LawfulMapM.mapM_id (f := List) g xs
    simp only [mapM_list, map_list] at this
    simp only [mapM_array, map_array, List.mapM_toArray, List.map_toArray, this]
    rfl

end DeriveMapM
