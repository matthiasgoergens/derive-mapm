module

public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util
public import DeriveMapM.Basic

-- all of it runs while `deriving MapM` and `deriving LawfulMapM` elaborate
@[expose] public meta section

/-!
# The `deriving MapM` handler

`deriving MapM` on an inductive type or a structure `T … ρ` whose last parameter `ρ : Type` is the
one to map writes, in `T`'s namespace:

* `T.map (g : ρ → σ) : T … ρ → T … σ`, a structural map;
* `T.mapM [Monad m] (g : ρ → m σ) : T … ρ → m (T … σ)`, with the effects in the order of the
  fields;
* the instances `MapM (T …)` and `Functor (T …)`, and the `simp` lemmas `T.map_class` and
  `T.mapM_class` that turn the class's `MapM.map` and `MapM.mapM` at `T` into `T.map` and `T.mapM`.

Other parameters before `ρ` stay as they are, an instance parameter as an instance.  A field is mapped
by its type:

* `ρ` itself: by `g`;
* `F τ`, where `F` does not mention `ρ` and has a `MapM` instance (`Option`, `List`, `Array`, and
  every type that derives `MapM`): by `MapM.map`, mapping each `τ` in it the same way;
* `α × β`: each side that mentions `ρ`;
* `T … ρ` itself, the type being defined, directly as a field (not inside another type): by a
  recursive call, which Lean checks as structural recursion;
* a type that does not mention `ρ`: left as it is, proofs included.

Anything else that mentions `ρ` is refused.  The errors about a field name it and its constructor
(an unnamed field is called so): `ρ` under a function arrow or in a proposition, an argument of a
type other than its last, a type without a `MapM` instance, and a field whose type depends on a field
that is mapped.  The others name the type: a nested inductive type (the type being defined inside
another type), an indexed or mutual family, a last parameter not of type `Type`, a type `T … ρ` not
itself of type `Type`, a `private` type, and a type that already declares one of the names the
handler writes.  Abbreviations (reducible definitions) in a field's type are unfolded first.

A structure's `map` applies its constructor to its projections (`T.mk x.a (g x.b) …`), an
inductive's is a `match` on its constructors, so that `simp [T.map]` unfolds either.
-/

namespace DeriveMapM.Handler

open Lean Elab Command Term Meta Deriving

/-- Whether the function written maps purely (`map`) or in a monad (`mapM`). -/
inductive Mode where
  | pure
  | monadic
  deriving BEq

/-- What writing the image of a field needs: the type, the parameter mapped, the parameters before it
(as the names the header binds), the mapping function and the function being defined. -/
structure Ctx where
  typeName : Name
  /-- The parameters of the type as the constructor's telescope binds them, `ρ` last. -/
  params : Array Expr
  rho : FVarId
  g : Ident
  self : Ident
  mode : Mode

/-- An error about the field `field` of the constructor `ctor`. -/
def fieldError {α : Type} (ctor : Name) (field : Name) (msg : MessageData) : TermElabM α :=
  if field.hasMacroScopes then
    throwError "deriving MapM: an unnamed field of {.ofConstName ctor}: {msg}"
  else
    throwError "deriving MapM: the field {field} of {.ofConstName ctor}: {msg}"

/-- The type of a field as the handler reads it: without `optParam` and `autoParam`, and with the
reducible definitions (`abbrev`s) at its head unfolded. -/
def fieldType (τ : Expr) : MetaM Expr := do
  whnfR (← instantiateMVars τ).cleanupAnnotations

/-- `bind e fun b => k b` for a monadic image, or `k e` for a pure one, so that a pure image is a
term and a monadic one a chain of binds that ends in `pure`. -/
def bindImage (c : Ctx) (e : Term) (k : Term → TermElabM Term) : TermElabM Term := do
  match c.mode with
  | .pure => k e
  | .monadic =>
    let b := mkIdent (← mkFreshUserName `b)
    let rest ← k b
    `($(mkCIdent ``Bind.bind) $e fun $b => $rest)

/-- The term that maps `a : τ`, for a `τ` that mentions `ρ`: of type `τ[σ/ρ]` when pure, `m τ[σ/ρ]`
when monadic.  `top` is whether `a` is a field itself, where a recursive occurrence of the type may
stand. -/
partial def image (c : Ctx) (ctor field : Name) (τ : Expr) (a : Term) (top : Bool) : TermElabM Term := do
  imageOf (← fieldType τ) a top
where
  imageOf : Expr → Term → Bool → TermElabM Term
  | .fvar x, a, _ => do
    if x == c.rho then `($(c.g) $a)
    else fieldError ctor field m!"unexpected variable in its type"
  | .app (.app (.const ``Prod _) α) β, a, _ => do
    let fst ← `($(mkCIdent ``Prod.fst) $a)
    let snd ← `($(mkCIdent ``Prod.snd) $a)
    let α ← fieldType α
    let β ← fieldType β
    let fst' ← if α.containsFVar c.rho then some <$> image c ctor field α fst false else pure none
    let snd' ← if β.containsFVar c.rho then some <$> image c ctor field β snd false else pure none
    let finish (x y : Term) : TermElabM Term := do
      match c.mode with
      | .pure => `(($x, $y))
      | .monadic => `($(mkCIdent ``Pure.pure) ($x, $y))
    match fst', snd' with
    | some x, some y => bindImage c x fun x => bindImage c y fun y => finish x y
    | some x, none => bindImage c x fun x => finish x snd
    | none, some y => bindImage c y fun y => finish fst y
    | none, none => fieldError ctor field m!"a pair that does not mention the parameter"
  | τ@(.app f x), a, top => do
    if τ.isAppOf c.typeName then
      let args := τ.getAppArgs
      unless top do
        fieldError ctor field m!"{τ} holds the type being defined inside another type (a nested \
          inductive type), which is not supported"
      unless args.size == c.params.size && (args.zip c.params).all fun (u, v) => u == v do
        fieldError ctor field m!"{τ} applies the type being defined to other parameters than its own"
      `($(c.self) $(c.g) $a)
    else
      if f.containsFVar c.rho then
        fieldError ctor field m!"the parameter is an argument of {τ} other than its last"
      let cls := mkApp (mkConst ``MapM) f
      unless ← isTypeCorrect cls do
        fieldError ctor field m!"{f} is not a type function Type → Type"
      -- The instance may rest on instance parameters of the type, which the functions bind with
      -- their binder kind (`paramBinders`), or on fields of class type, which their pattern binds as
      -- local instances (a structure with such a field is mapped by a `match`, `useMatch`).
      if (← synthInstance? cls).isNone then
        fieldError ctor field m!"{τ} has no instance of MapM ({f}): derive MapM for it or write one"
      let inner : Term ← match x with
        | .fvar y => if y == c.rho then pure c.g else
            fieldError ctor field m!"unexpected variable in its type"
        | _ => do
          let y := mkIdent (← mkFreshUserName `y)
          let body ← image c ctor field x y false
          `(fun $y => $body)
      match c.mode with
      | .pure => `($(mkCIdent ``MapM.map) $inner $a)
      | .monadic => `($(mkCIdent ``MapM.mapM) $inner $a)
  | .forallE .., _, _ => fieldError ctor field m!"the parameter appears under a function arrow"
  | τ, _, _ => fieldError ctor field m!"its type {τ} is not supported"

/-- The constructor application with the fields `args`, mapped where their type mentions `ρ`: `fields`
are the constructor's fields (local variables), `args` the terms that hold their values. -/
def ctorImage (c : Ctx) (ctor : Name) (paramArgs : Array Term) (sigma : Ident) (fields : Array Expr)
    (args : Array Term) : TermElabM Term := do
  -- which fields are mapped, refusing a field whose type depends on a mapped one
  let mut mapped : Array FVarId := #[]
  let mut images : Array (Option Term) := #[]
  for (x, a) in fields.zip args do
    let .fvar id := x | throwError "deriving MapM: a field of {.ofConstName ctor} is not a variable"
    let decl ← id.getDecl
    let τ ← fieldType decl.type
    if mapped.any τ.containsFVar then
      fieldError ctor decl.userName m!"its type depends on a field that is mapped"
    if τ.containsFVar c.rho then
      if ← isProp τ then
        fieldError ctor decl.userName m!"a proposition that mentions the parameter"
      mapped := mapped.push id
      images := images.push (some (← image c ctor decl.userName τ a true))
    else
      images := images.push none
  let finish (acc : Array Term) : TermElabM Term := do
    let app ← `(@$(mkCIdent ctor) $paramArgs* $sigma $acc*)
    match c.mode with
    | .pure => pure app
    | .monadic => `($(mkCIdent ``Pure.pure) $app)
  let rec go : List (Option Term × Term) → Array Term → TermElabM Term
    | [], acc => finish acc
    | (some e, _) :: rest, acc => bindImage c e fun b => go rest (acc.push b)
    | (none, a) :: rest, acc => go rest (acc.push a)
  go (images.zip args).toList #[]

/-- The binders of the parameters before the one mapped, named `argNames`: implicit, but an instance
parameter as an instance binder with its type, so that the code written can use it. -/
def paramBinders (indVal : InductiveVal) (argNames : Array Name) :
    TermElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) :=
  forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut lctx ← getLCtx
    for (x, n) in xs.zip argNames do
      if let .fvar id := x then lctx := lctx.setUserName id n
    withLCtx lctx (← getLocalInstances) do
      let mut binders := #[]
      for (x, n) in (xs.zip argNames).pop do
        let .fvar id := x | throwError "deriving MapM: a parameter of {.ofConstName indVal.name} is not a variable"
        let decl ← id.getDecl
        if decl.binderInfo.isInstImplicit then
          let ty ← withOptions (fun o => (o.setBool `pp.sanitizeNames false).setBool `pp.explicit true) do
            PrettyPrinter.delab decl.type
          binders := binders.push (← `(Parser.Term.bracketedBinderF| [$(mkIdent n) : $ty]))
        else
          binders := binders.push (← `(Parser.Term.bracketedBinderF| {$(mkIdent n)}))
      pure binders

/-- Whether a structure is mapped by a `match` rather than its projections: when a field is of class
type, which the code written needs bound as a local instance, holds the structure itself, which a
recursive call on a projection would not show to be structural, or is private, since a module's
exposed definitions may not name a private projection. -/
def useMatch (indVal : InductiveVal) : TermElabM Bool := do
  unless isStructure (← getEnv) indVal.name do return true
  if let some info := getStructureInfo? (← getEnv) indVal.name then
    if info.fieldInfo.any (isPrivateName ·.projFn) then return true
  let some ctor := indVal.ctors.head? | return true
  let ctorVal ← getConstInfoCtor ctor
  forallTelescopeReducing ctorVal.type fun xs _ => do
    for x in xs.extract indVal.numParams xs.size do
      if (← isClass? (← inferType x)).isSome then return true
      if (← fieldType (← inferType x)).isAppOf indVal.name then return true
    return false

/-- The definition of `T.map` or `T.mapM`. -/
def mkFunction (indVal : InductiveVal) (mode : Mode) : TermElabM Command := do
  let typeName := indVal.name
  let fnName := typeName ++ (match mode with | .pure => `map | .monadic => `mapM)
  let argNames ← mkInductArgNames indVal
  -- the parameters before the one mapped, which the instance and the functions bind implicitly
  let others : Array Ident := argNames.pop.map mkIdent
  let rho := mkIdent `α
  let sigma := mkIdent `β
  let m := mkIdent `m
  let g := mkIdent `g
  let x := mkIdent `x
  let T := mkCIdent typeName
  let otherBinders ← paramBinders indVal argNames
  let source ← `(@$T $others* $rho)
  let target ← `(@$T $others* $sigma)
  let self := mkIdent fnName
  let body ← if ← useMatch indVal then
      inductiveBody indVal x sigma others g self
    else
      structureBody typeName indVal x sigma others g self
  let name := mkIdent (`_root_ ++ fnName)
  match mode with
  | .pure =>
    `(/-- The value with each value of its last parameter mapped by `g` (`deriving MapM`). -/
      def $name $otherBinders:bracketedBinder* {$rho $sigma : Type} ($g : $rho → $sigma) ($x : $source) :
        $target := $body)
  | .monadic =>
    `(/-- The value with each value of its last parameter mapped by `g` in the monad, in the order of
        the fields (`deriving MapM`). -/
      def $name $otherBinders:bracketedBinder* {$rho $sigma : Type} {$m : Type → Type} [Monad $m]
        ($g : $rho → $m $sigma) ($x : $source) : $m $target := $body)
where
  /-- The context for the constructor `ctor`'s telescope `xs`. -/
  ctx (xs : Array Expr) (g self : Ident) : TermElabM Ctx := do
    let params := xs.extract 0 indVal.numParams
    let some rho := params.back? | throwError "deriving MapM: {.ofConstName indVal.name} has no parameter"
    let .fvar rhoId := rho | throwError "deriving MapM: a parameter of {.ofConstName indVal.name} is not a variable"
    pure { typeName := indVal.name, params, rho := rhoId, g, self, mode }
  /-- A structure's body, by its projections. -/
  structureBody (typeName : Name) (indVal : InductiveVal) (x sigma : Ident) (others : Array Ident)
      (g self : Ident) : TermElabM Term := do
    let some ctor := indVal.ctors.head? | throwError "deriving MapM: {.ofConstName typeName} has no constructor"
    let ctorVal ← getConstInfoCtor ctor
    forallTelescopeReducing ctorVal.type fun xs _ => do
      let c ← ctx xs g self
      let fields := xs.extract indVal.numParams xs.size
      let args ← fields.mapM fun field => do
        let name ← match field with
          | .fvar id => pure (← id.getDecl).userName
          | _ => throwError "deriving MapM: a field of {.ofConstName typeName} is not a variable"
        `($x.$(mkIdent name):ident)
      ctorImage c ctor (others.map fun p => (p : Term)) sigma fields args
  /-- An inductive type's body (or a structure's with a field of class type), by a `match` on its
  constructors. -/
  inductiveBody (indVal : InductiveVal) (x sigma : Ident) (others : Array Ident) (g self : Ident) :
      TermElabM Term := do
    let alts ← indVal.ctors.toArray.mapM fun ctor => do
      let ctorVal ← getConstInfoCtor ctor
      forallTelescopeReducing ctorVal.type fun xs _ => do
        let c ← ctx xs g self
        let fields := xs.extract indVal.numParams xs.size
        let names ← fields.mapM fun _ => do pure (mkIdent (← mkFreshUserName `a))
        let holes ← (Array.range indVal.numParams).mapM fun _ => `(_)
        let pat ← `(@$(mkCIdent ctor) $holes* $names*)
        let rhs ← ctorImage c ctor (others.map fun p => (p : Term)) sigma fields (names.map fun n => (n : Term))
        `(Parser.Term.matchAltExpr| | $pat => $rhs)
    if alts.isEmpty then `(nomatch $x:ident) else `(match $x:ident with $alts:matchAlt*)

/-- The names `deriving MapM` declares in the namespace of the type. -/
def mapMNames : List Name := [`map, `mapM, `map_class, `mapM_class]

/-- The names `deriving LawfulMapM` declares in the namespace of the type. -/
def lawfulMapMNames : List Name := [`map_id, `map_map, `mapM_id]

/-- Refuses a type whose last parameter is not of type `Type`, which is not itself of type `Type`
once applied to its parameters, or which already declares a name in `names`. -/
def checkShape (indVal : InductiveVal) (names : List Name := mapMNames) : TermElabM Unit := do
  forallBoundedTelescope indVal.type indVal.numParams fun xs sort => do
    let some rho := xs.back? | throwError "deriving MapM: {.ofConstName indVal.name} has no parameter"
    unless (← whnf (← inferType rho)) == mkSort Level.one do
      throwError "deriving MapM: the last parameter of {.ofConstName indVal.name} has type \
        {← inferType rho}, not Type"
    unless (← whnf sort) == mkSort Level.one do
      throwError "deriving MapM: {.ofConstName indVal.name} applied to its parameters is of type {sort}, \
        not Type"
  for name in names do
    if (← getEnv).contains (indVal.name ++ name) then
      throwError "deriving MapM: {.ofConstName indVal.name} already declares {indVal.name ++ name}"

/-- The commands `deriving MapM` runs for the type `typeName`. -/
def mkCommands (typeName : Name) : TermElabM (Array Command) := do
  let indVal ← getConstInfoInduct typeName
  if indVal.all.length > 1 then
    throwError "deriving MapM: {.ofConstName typeName} is one of a mutual family, which is not supported"
  if indVal.numIndices > 0 then
    throwError "deriving MapM: {.ofConstName typeName} is an indexed family, which is not supported"
  if indVal.isNested then
    throwError "deriving MapM: {.ofConstName typeName} is a nested inductive type, which is not supported"
  if indVal.numParams == 0 then
    throwError "deriving MapM: {.ofConstName typeName} has no parameter to map"
  if isPrivateName typeName then
    throwError "deriving MapM: {.ofConstName typeName} is private, which is not supported"
  checkShape indVal
  let mapFn ← mkFunction indVal .pure
  let mapMFn ← mkFunction indVal .monadic
  let argNames ← mkInductArgNames indVal
  let others : Array Ident := argNames.pop.map mkIdent
  let binders ← paramBinders indVal argNames
  let T := mkCIdent typeName
  let F ← `(@$T $others*)
  let map := mkCIdent (typeName ++ `map)
  let mapM := mkCIdent (typeName ++ `mapM)
  let mapClass := mkIdent (`_root_ ++ typeName ++ `map_class)
  let mapMClass := mkIdent (`_root_ ++ typeName ++ `mapM_class)
  let a := mkIdent `α
  let b := mkIdent `β
  let m := mkIdent `m
  let g := mkIdent `g
  let x := mkIdent `x
  let mapMInst ← `(instance $binders:bracketedBinder* : $(mkCIdent ``MapM) $F where
      map := $map
      mapM := $mapM)
  let functorInst ← `(instance $binders:bracketedBinder* : Functor $F where
      map := $map)
  let mapEq ← `(/-- The class's `map` is the derived one (`deriving MapM`). -/
    @[simp] theorem $mapClass $binders:bracketedBinder* {$a $b : Type} ($g : $a → $b) ($x : $F $a) :
      $(mkCIdent ``MapM.map) $g $x = $map $g $x := rfl)
  let mapMEq ← `(/-- The class's `mapM` is the derived one (`deriving MapM`). -/
    @[simp] theorem $mapMClass $binders:bracketedBinder* {$a $b : Type} {$m : Type → Type} [Monad $m]
      ($g : $a → $m $b) ($x : $F $a) : $(mkCIdent ``MapM.mapM) $g $x = $mapM $g $x := rfl)
  pure #[mapFn, mapMFn, mapMInst, functorInst, mapEq, mapMEq]

/-- The handler of `deriving MapM`. -/
def mapMHandler (typeNames : Array Name) : CommandElabM Bool := do
  for typeName in typeNames do
    unless ← isInductive typeName do
      return false
    let cmds ← liftTermElabM (mkCommands typeName)
    for cmd in cmds do
      elabCommand cmd
  return true

/-- The type functions `F` through which a field of type `τ` is mapped (`image`), the parameter `rho`
in their argument. -/
partial def containers (rho : FVarId) (τ : Expr) : MetaM (Array Expr) := do
  match ← fieldType τ with
  | .app (.app (.const ``Prod _) α) β =>
    let l ← if α.containsFVar rho then containers rho α else pure #[]
    let r ← if β.containsFVar rho then containers rho β else pure #[]
    pure (l ++ r)
  | .app f x =>
    if x.containsFVar rho && !f.containsFVar rho then pure (#[f] ++ (← containers rho x)) else pure #[]
  | _ => pure #[]

/-- Refuses a type whose fields hold the parameter inside a type function without a `LawfulMapM`
instance, whose laws the proofs of `deriving LawfulMapM` need. -/
def checkLawfulFields (indVal : InductiveVal) : TermElabM Unit := do
  for ctor in indVal.ctors do
    let ctorVal ← getConstInfoCtor ctor
    forallTelescopeReducing ctorVal.type fun xs _ => do
      let some (.fvar rho) := (xs.extract 0 indVal.numParams).back? | pure ()
      for x in xs.extract indVal.numParams xs.size do
        let .fvar id := x | pure ()
        let decl ← id.getDecl
        for f in ← containers rho decl.type do
          if f.isAppOf indVal.name then continue
          let found ← match ← synthInstance? (mkApp (mkConst ``MapM) f) with
            | some inst => pure (← synthInstance? (mkApp2 (mkConst ``LawfulMapM) f inst)).isSome
            | none => pure false
          unless found do
            if f.isFVar then
              throwError "deriving LawfulMapM: the field {decl.userName} of {MessageData.ofConstName ctor} \
                holds the type parameter {f}, whose laws the proofs cannot assume: deriving LawfulMapM \
                does not support it"
            throwError "deriving LawfulMapM: the field {decl.userName} of {MessageData.ofConstName ctor} \
              holds {f}, which has no LawfulMapM instance: derive LawfulMapM for it first"

/-- `by simp [lemmas]`. -/
def simpBy (lemmas : Array Term) : TermElabM Term := do
  let args : Array (TSyntax [``Parser.Tactic.simpStar, ``Parser.Tactic.simpErase, ``Parser.Tactic.simpLemma]) ←
    lemmas.mapM fun t => do pure ⟨(← `(Parser.Tactic.simpLemma| $t:term)).raw⟩
  `(by simp [$args,*])

/-- A proof of a law for every value `x`, by a `match` on its constructors (structural recursion), each
case proved by `rhs` given the fields that are recursive occurrences of the type, whose cases of
the law it uses.  No `simp_all`: the cases' hypotheses (proof fields) stay out of the simp set. -/
def lawBody (indVal : InductiveVal) (x : Ident) (rhs : Array Term → TermElabM Term) : TermElabM Term := do
  let alts ← indVal.ctors.toArray.mapM fun ctor => do
    let ctorVal ← getConstInfoCtor ctor
    forallTelescopeReducing ctorVal.type fun xs _ => do
      let fields := xs.extract indVal.numParams xs.size
      let some (.fvar rho) := (xs.extract 0 indVal.numParams).back? | throwError "deriving MapM: \
        {.ofConstName indVal.name} has no parameter"
      let names ← fields.mapM fun _ => do pure (mkIdent (← mkFreshUserName `a))
      let mut recs : Array Term := #[]
      for (field, n) in fields.zip names do
        let τ ← fieldType (← inferType field)
        if τ.isAppOf indVal.name && τ.containsFVar rho then recs := recs.push n
      let holes ← (Array.range indVal.numParams).mapM fun _ => `(_)
      let pat ← `(@$(mkCIdent ctor) $holes* $names*)
      `(Parser.Term.matchAltExpr| | $pat => $(← rhs recs))
  if alts.isEmpty then `(fun $x => nomatch $x:ident) else `(fun $x => match $x:ident with $alts:matchAlt*)

/-- The commands `deriving LawfulMapM` runs for the type `typeName`, which derives `MapM`: the laws
for `T.map` and `T.mapM`, as `simp` lemmas, and the instance `LawfulMapM (T …)`.  Each is proved by
structural recursion on the value and `simp` per constructor, with the laws of the types its fields
hold in the simp set (those of `Option`, `List`, `Array`, every type that derives `LawfulMapM`, and
the class's laws for instances written by hand). -/
def mkLawfulCommands (typeName : Name) : TermElabM (Array Command) := do
  let indVal ← getConstInfoInduct typeName
  checkShape indVal lawfulMapMNames
  checkLawfulFields indVal
  let argNames ← mkInductArgNames indVal
  let others : Array Ident := argNames.pop.map mkIdent
  let binders ← paramBinders indVal argNames
  let T := mkCIdent typeName
  let F ← `(@$T $others*)
  let map := mkCIdent (typeName ++ `map)
  let mapM := mkCIdent (typeName ++ `mapM)
  let mapId := typeName ++ `map_id
  let mapMap := typeName ++ `map_map
  let mapMId := typeName ++ `mapM_id
  let a := mkIdent `α
  let b := mkIdent `β
  let c := mkIdent `γ
  let g := mkIdent `g
  let h := mkIdent `h
  let x := mkIdent `x
  let y := mkIdent (← mkFreshUserName `y)
  let comp := mkCIdent ``Function.comp_def
  -- the laws of the instances written by hand, which have no simp lemmas of their own
  let lawId := mkCIdent ``LawfulMapM.map_id
  let lawMap := mkCIdent ``LawfulMapM.map_map
  let lawMId := mkCIdent ``LawfulMapM.mapM_id
  let mapIdThm ← `(/-- `map` keeps a value under the identity (`deriving LawfulMapM`). -/
    @[simp] theorem $(mkIdent (`_root_ ++ mapId)) $binders:bracketedBinder* {$a : Type} :
        ∀ ($x : $F $a), $map (fun $y => $y) $x = $x :=
      $(← lawBody indVal x fun recs => do
          let recs ← recs.mapM fun r => `($(mkIdent mapId) $r)
          simpBy (#[(map : Term), lawId] ++ recs)))
  let mapMapThm ← `(/-- `map` composes (`deriving LawfulMapM`). -/
    @[simp] theorem $(mkIdent (`_root_ ++ mapMap)) $binders:bracketedBinder* {$a $b $c : Type} ($g : $a → $b)
        ($h : $b → $c) : ∀ ($x : $F $a), $map $h ($map $g $x) = $map (fun $y => $h ($g $y)) $x :=
      $(← lawBody indVal x fun recs => do
          let recs ← recs.mapM fun r => `($(mkIdent mapMap) $g $h $r)
          simpBy (#[(map : Term), comp, lawMap] ++ recs)))
  let mapMIdThm ← `(/-- `mapM` in `Id` is `map` (`deriving LawfulMapM`). -/
    @[simp] theorem $(mkIdent (`_root_ ++ mapMId)) $binders:bracketedBinder* {$a $b : Type} ($g : $a → $b) :
        ∀ ($x : $F $a), $mapM (m := Id) (fun $y => pure ($g $y)) $x = pure ($map $g $x) :=
      $(← lawBody indVal x fun recs => do
          let recs ← recs.mapM fun r => `($(mkIdent mapMId) $g $r)
          simpBy (#[(mapM : Term), map, lawMId] ++ recs)))
  let inst ← `(instance $binders:bracketedBinder* : $(mkCIdent ``LawfulMapM) $F where
      map_id := $(mkCIdent mapId)
      map_map := $(mkCIdent mapMap)
      mapM_id := $(mkCIdent mapMId))
  pure #[mapIdThm, mapMapThm, mapMIdThm, inst]

/-- The handler of `deriving LawfulMapM`, for a type that derives `MapM` (before it, in the same
clause or earlier). -/
def lawfulMapMHandler (typeNames : Array Name) : CommandElabM Bool := do
  for typeName in typeNames do
    unless ← isInductive typeName do
      return false
    -- `T.map_class` is a theorem when `deriving MapM` wrote it; a field of that name is a definition.
    -- Looked up in the private view: in a module's public view a theorem is an axiom.
    unless ((← getEnv).setExporting false).find? (typeName ++ `map_class) matches some (.thmInfo _) do
      throwError "deriving LawfulMapM: {.ofConstName typeName} does not derive MapM: write \
        `deriving MapM, LawfulMapM`"
    for cmd in ← liftTermElabM (mkLawfulCommands typeName) do
      elabCommand cmd
  return true

initialize
  registerDerivingHandler ``MapM mapMHandler
  registerDerivingHandler ``LawfulMapM lawfulMapMHandler

end DeriveMapM.Handler
