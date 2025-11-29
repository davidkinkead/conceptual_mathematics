import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory

set_option maxHeartbeats 400000 -- required for Exercise 17.4(c)


#doc (Manual) "Session 17: Some uses of graphs" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. Paths

In the exercises that follow for this Session, we implement the free category 𝑭$`(G)` on each graph $`G` using mathlib's `CategoryTheory.Paths V`, where `V` is a quiver (i.e., a directed graph). In particular, we make extensive use of the inductive datatype `Quiver.Path`, the type of paths through the arrows of the quiver, which we print below for reference.

```lean (name := out_Quiver_Path)
#print Quiver.Path
```

```leanOutput out_Quiver_Path
inductive Quiver.Path.{v, u} : {V : Type u} → [Quiver V] → V → V → Sort (max (u + 1) v)
number of parameters: 3
constructors:
Quiver.Path.nil : {V : Type u} → [inst : Quiver V] → {a : V} → Quiver.Path a a
Quiver.Path.cons : {V : Type u} → [inst : Quiver V] → {a b c : V} → Quiver.Path a b → (b ⟶ c) → Quiver.Path a c
```

:::question (questionTitle := "Exercise 1") (questionPage := "200")
Danilo noticed that from a graph $`G` we can build a category 𝑭$`(G)`, the _free category on the graph_ $`G`. An object is a dot of $`G`, and a map is a path in $`G`. For which of the following graphs does Danilo's category have a terminal object?
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 17.1 (p. 200)
```

An object $`S` is terminal in a category if for each object $`X` in the category there is exactly one map from $`X` to $`S`. Only the free category 𝑭$`(G_b)` on the graph (b) and the free category 𝑭$`(G_c)` on the graph (c) have objects that meet this criterion.

\(a\) 𝑭$`(G_a)` has infinitely many maps from the object to itself (each map corresponding to the path formed by going around the arrow/loop a different number of times).

```savedLean -show
namespace Ex17_1_a
```

```savedLean
inductive Dot
  | x₁

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₁

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  by_contra h
  have h_uniq : Unique (Quiver.Path Dot.x₁ Dot.x₁) :=
    uniqueToTerminal (C := Paths Dot) Dot.x₁
  have h_sub : Subsingleton (Quiver.Path Dot.x₁ Dot.x₁) :=
    inferInstance
  have h_nontriv : Nontrivial (Quiver.Path Dot.x₁ Dot.x₁) := by
    apply nontrivial_iff.mpr
    use Quiver.Path.nil, (Quiver.Hom.toPath Arrow.f₁)
    intro
    contradiction
  exact false_of_nontrivial_of_subsingleton
      (Quiver.Path Dot.x₁ Dot.x₁)
```

```savedLean -show
end Ex17_1_a
```

\(b\) The only object in 𝑭$`(G_b)` is terminal, since there is exactly one map from that object to itself, namely the identity map.

```savedLean -show
namespace Ex17_1_b
```

```savedLean
inductive Dot
  | x₁

inductive Arrow : Dot → Dot → Type

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : HasTerminal (Paths Dot) := by
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ Dot.x₁) := by
    intro x
    apply Subsingleton.intro
    intro f g
    let P : {x : Paths Dot} → (x ⟶ Dot.x₁) → Prop :=
      fun p => p = Quiver.Path.nil
    have h_all_eq_id : ∀ {x : Paths Dot} (p : x ⟶ Dot.x₁), P p := by
      intros
      apply Paths.induction_fixed_target
      · rfl
      · intro _ _ _ e _
        nomatch e
    rw [h_all_eq_id f, h_all_eq_id g]
  have h_all_nonempty
      : ∀ (x : Paths Dot), Nonempty (x ⟶ Dot.x₁) := by
    intro x
    exact Nonempty.intro Quiver.Path.nil
  exact hasTerminal_of_unique (C := Paths Dot) Dot.x₁
```

```savedLean -show
end Ex17_1_b
```

\(c\) In 𝑭$`(G_c)`, the second dot from the right corresponds to a terminal object, since there is exactly one map (path) to that object from every object in 𝑭$`(G_c)`. We label the dots from left to right, with $`x_1` being the upper left dot and $`x_2` the lower left dot (so $`x_4` is terminal).

```savedLean -show
namespace Ex17_1_c
```

```savedLean
inductive Dot
  | x₁ | x₂ | x₃ | x₄ | x₅

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₃
  | f₂ : Arrow .x₂ .x₃
  | f₃ : Arrow .x₃ .x₄
  | f₅ : Arrow .x₅ .x₄

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : HasTerminal (Paths Dot) := by
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ Dot.x₄) := by
    intro x
    apply Subsingleton.intro
    intro f g
    cases x
    all_goals (
      repeat first
      | (rcases f with _ | ⟨f, _, _⟩) -- deconstruct f
      | (rcases g with _ | ⟨g, _, _⟩) -- deconstruct g
      | contradiction
      | rfl
    )
  have h_all_nonempty
      : ∀ (x : Paths Dot), Nonempty (x ⟶ Dot.x₄) := by
    intro x
    cases x
    · exact Nonempty.intro
          ((Quiver.Hom.toPath Arrow.f₁).cons Arrow.f₃)
    · exact Nonempty.intro
          ((Quiver.Hom.toPath Arrow.f₂).cons Arrow.f₃)
    · exact Nonempty.intro
          (Quiver.Hom.toPath Arrow.f₃)
    · exact Nonempty.intro
          Quiver.Path.nil
    · exact Nonempty.intro
          (Quiver.Hom.toPath Arrow.f₅)
  exact hasTerminal_of_unique (C := Paths Dot) Dot.x₄
```

```savedLean -show
end Ex17_1_c
```

\(d\) 𝑭$`(G_d)` is similar to 𝑭$`(G_a)` in that each object of 𝑭$`(G_d)` has infinitely many maps from itself to itself and from the other object to itself (each map corresponding to the path formed by going a different number of times around the closed loop of arrows between the two objects).

```savedLean -show
namespace Ex17_1_d
```

```savedLean
inductive Dot
  | x₁ | x₂

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₂
  | f₂ : Arrow .x₂ .x₁

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  by_contra h
  have h_all_uniq
      : ∀ (x : Paths Dot), Unique (x ⟶ ⊤_ Paths Dot) := by
    intro x
    exact uniqueToTerminal x
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ ⊤_ Paths Dot) := by
    intro x
    infer_instance
  have h_nontriv₁ : Nontrivial (Quiver.Path Dot.x₁ Dot.x₁) := by
    apply nontrivial_iff.mpr
    use Quiver.Path.nil, ((Quiver.Hom.toPath Arrow.f₁).cons Arrow.f₂)
    intro
    contradiction
  have h_nontriv₂ : Nontrivial (Quiver.Path Dot.x₂ Dot.x₂) := by
    apply nontrivial_iff.mpr
    use Quiver.Path.nil, ((Quiver.Hom.toPath Arrow.f₂).cons Arrow.f₁)
    intro
    contradiction
  cases hx : ⊤_ (Paths Dot) <;> rw [hx] at h_all_sub
  · exact false_of_nontrivial_of_subsingleton
        (Quiver.Path Dot.x₁ Dot.x₁)
  · exact false_of_nontrivial_of_subsingleton
        (Quiver.Path Dot.x₂ Dot.x₂)
```

```savedLean -show
end Ex17_1_d
```

\(e\) In 𝑭$`(G_e)`, the left-hand object has no map from the right-hand object, while the right-hand object has two maps from the left-hand object. We label the dots from left to right.

```savedLean -show
namespace Ex17_1_e
```

```savedLean
inductive Dot
  | x₁ | x₂

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₂
  | f₂ : Arrow .x₁ .x₂

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  by_contra h
  have h_all_uniq
      : ∀ (x : Paths Dot), Unique (x ⟶ ⊤_ Paths Dot) := by
    intro x
    exact uniqueToTerminal x
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ ⊤_ Paths Dot) := by
    intro x
    infer_instance
  have h_empty₁ : ¬(Nonempty (Quiver.Path Dot.x₂ Dot.x₁)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    nomatch p
  have h_nontriv₂ : Nontrivial (Quiver.Path Dot.x₁ Dot.x₂) := by
    apply nontrivial_iff.mpr
    use (Quiver.Hom.toPath Arrow.f₁), (Quiver.Hom.toPath Arrow.f₂)
    intro H
    injection H with _ h_arrow
    contradiction
  cases hx : ⊤_ (Paths Dot)
  · rw [hx] at h_all_uniq h_all_sub
    have h_uniq₁ : Unique (Quiver.Path Dot.x₂ Dot.x₁) :=
      h_all_uniq Dot.x₂
    have h_nonempty₁ : Nonempty (Quiver.Path Dot.x₂ Dot.x₁) := by
      infer_instance
    contradiction
  · rw [hx] at h_all_sub
    exact false_of_nontrivial_of_subsingleton
        (Quiver.Path Dot.x₁ Dot.x₂)
```

```savedLean -show
end Ex17_1_e
```

\(f\) In 𝑭$`(G_f)`, neither the leftmost object nor the centre object has a map from the rightmost object, while the rightmost object has no map from either the leftmost object nor the centre object. We label the dots from left to right again.

```savedLean -show
namespace Ex17_1_f
```

```savedLean
inductive Dot
  | x₁ | x₂ | x₃

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₂ .x₁

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  by_contra h
  have h_all_uniq
      : ∀ (x : Paths Dot), Unique (x ⟶ ⊤_ Paths Dot) := by
    intro x
    exact uniqueToTerminal x
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ ⊤_ Paths Dot) := by
    intro x
    infer_instance
  have h_empty₁ : ¬(Nonempty (Quiver.Path Dot.x₃ Dot.x₁)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    match p with
    | .cons p' q =>
      match p' with
      | .nil =>
      nomatch q
  have h_empty₂ : ¬(Nonempty (Quiver.Path Dot.x₃ Dot.x₂)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    nomatch p
  have h_empty₃ : ¬(Nonempty (Quiver.Path Dot.x₂ Dot.x₃)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    nomatch p
  cases hx : ⊤_ (Paths Dot) <;> rw [hx] at h_all_uniq h_all_sub
  · have h_uniq₁ : Unique (Quiver.Path Dot.x₃ Dot.x₁) :=
      h_all_uniq Dot.x₃
    have h_nonempty₂ : Nonempty (Quiver.Path Dot.x₃ Dot.x₁) := by
      infer_instance
    contradiction
  · have h_uniq₂ : Unique (Quiver.Path Dot.x₃ Dot.x₂) :=
      h_all_uniq Dot.x₃
    have h_nonempty₂ : Nonempty (Quiver.Path Dot.x₃ Dot.x₂) := by
      infer_instance
    contradiction
  · have h_uniq₃ : Unique (Quiver.Path Dot.x₂ Dot.x₃) :=
      h_all_uniq Dot.x₂
    have h_nonempty₃ : Nonempty (Quiver.Path Dot.x₂ Dot.x₃) := by
      infer_instance
    contradiction
```

```savedLean -show
end Ex17_1_f
```
:::

# 3. Commuting diagrams

:::definition (definitionTerm := "Commutes") (definitionPage := "201")
We say that a diagram of shape $`G` in 𝒞 _commutes_ if for each pair $`p`, $`q` of dots in $`G`, all paths in $`G` from $`p` to $`q` are interpreted as the same map in 𝒞.
:::

The "interpretation" of dots in $`G` as objects of 𝒞 and paths in $`G` as maps of 𝒞 is performed by a functor from the free category 𝑭$`(G)` to 𝒞, written in Lean as `CategoryTheory.Paths Dot ⥤ 𝒞`, where `p q : Dot`.

:::question (questionTitle := "Exercise 2") (questionPage := "202")
```savedComment
Exercise 17.2 (p. 202)
```

```savedLean -show
namespace Ex17_2
```

Show that a diagram of shape

```savedLean
inductive Dot
  | x₁ | x₂

inductive Arrow : Dot → Dot → Type
  | f : Arrow .x₁ .x₂
  | g : Arrow .x₂ .x₁

instance : Quiver Dot where
  Hom := Arrow
```

commutes if and only if the maps assigned to the two arrows are inverse.
:::

:::solution (solutionTo := "Exercise 2")
We need to show that under a functor from the free category 𝑭$`(G)` to 𝒞, all paths between each pair of dots in 𝑭$`(G)` correspond to the same map in 𝒞 if and only if the two arrows in the graph correspond to inverse maps in 𝒞. Since there are four possible pairings of dots, the proof of the backward ("if") direction contains four parts.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Dot ⥤ 𝒞) :

    -- Let x₁' be the object in 𝒞 associated with Dot.x₁ in 𝐹(G)
    let x₁' : 𝒞 := F.obj Dot.x₁
    -- Let x₂' be the object in 𝒞 associated with Dot.x₂ in 𝐹(G)
    let x₂' : 𝒞 := F.obj Dot.x₂
    -- Let f' be the morphism in 𝒞 associated with Arrow.f in 𝐹(G)
    let f' : x₁' ⟶ x₂' := F.map (Quiver.Hom.toPath Arrow.f)
    -- Let g' be the morphism in 𝒞 associated with Arrow.g in 𝐹(G)
    let g' : x₂' ⟶ x₁' := F.map (Quiver.Hom.toPath Arrow.g)

    -- Dot.x₁ ⟶ Dot.x₁ is interpreted as the identity on x₁' in 𝒞
    (∀ p₁ : Quiver.Path Dot.x₁ Dot.x₁, F.map p₁ = 𝟙 x₁') ∧
    -- Dot.x₂ ⟶ Dot.x₂ is interpreted as the identity on x₂' in 𝒞
    (∀ p₂ : Quiver.Path Dot.x₂ Dot.x₂, F.map p₂ = 𝟙 x₂') ∧
    -- Dot.x₁ ⟶ Dot.x₂ is interpreted as f' in 𝒞
    (∀ p₁₂ : Quiver.Path Dot.x₁ Dot.x₂, F.map p₁₂ = f') ∧
    -- Dot.x₂ ⟶ Dot.x₁ is interpreted as g' in 𝒞
    (∀ p₂₁ : Quiver.Path Dot.x₂ Dot.x₁, F.map p₂₁ = g') ↔
    -- The maps assigned to the two arrows in G are inverse
    g' ⊚ f' = 𝟙 x₁' ∧ f' ⊚ g' = 𝟙 x₂' := by

  constructor
  -- Proof of the forward ("only if") direction
  · repeat rw [← F.map_comp]
    intro ⟨h₁, h₂, h₁₂, h₂₁⟩
    constructor
    · rw [h₁]
    · rw [h₂]
  -- Proof of the backward ("if") direction
  · repeat rw [← F.map_comp]
    intro ⟨h₁, h₂⟩
    and_intros
    -- ∀ p₁ : Quiver.Path Dot.x₁ Dot.x₁, F.map p₁ = 𝟙 x₁'
    · let rec aux₁ (p : Quiver.Path Dot.x₁ Dot.x₁)
          : F.map p = 𝟙 (F.obj Dot.x₁) := by
        match p with
        | .nil =>
          exact F.map_id Dot.x₁
        | .cons tail Arrow.g =>
          match tail with
          | .cons tail' Arrow.f =>
            change F.map ((Quiver.Hom.toPath Arrow.g ⊚
                           Quiver.Hom.toPath Arrow.f) ⊚ tail') = _
            rw [Functor.map_comp, h₁, Category.comp_id]
            exact aux₁ tail'
      intro p
      exact aux₁ p
    -- ∀ p₂ : Quiver.Path Dot.x₂ Dot.x₂, F.map p₂ = 𝟙 x₂'
    · let rec aux₂ (p : Quiver.Path Dot.x₂ Dot.x₂)
          : F.map p = 𝟙 (F.obj Dot.x₂) := by
        match p with
        | .nil =>
          exact F.map_id Dot.x₂
        | .cons tail Arrow.f =>
          match tail with
          | .cons tail' Arrow.g =>
            change F.map ((Quiver.Hom.toPath Arrow.f ⊚
                           Quiver.Hom.toPath Arrow.g) ⊚ tail') = _
            rw [Functor.map_comp, h₂, Category.comp_id]
            exact aux₂ tail'
      intro p
      exact aux₂ p
    -- ∀ p₁₂ : Quiver.Path Dot.x₁ Dot.x₂, F.map p₁₂ = f'
    · let rec aux₁₂ (p : Quiver.Path Dot.x₁ Dot.x₂)
          : F.map p = F.map (Quiver.Hom.toPath Arrow.f) := by
        match p with
        | .cons tail Arrow.f =>
          match tail with
          | .nil =>
            rfl
          | .cons tail' Arrow.g =>
            change F.map ((Quiver.Hom.toPath Arrow.f ⊚
                           Quiver.Hom.toPath Arrow.g) ⊚ tail') = _
            rw [Functor.map_comp, h₂, Category.comp_id]
            exact aux₁₂ tail'
      intro p
      exact aux₁₂ p
    -- ∀ p₂₁ : Quiver.Path Dot.x₂ Dot.x₁, F.map p₂₁ = g'
    · let rec aux₂₁ (p : Quiver.Path Dot.x₂ Dot.x₁)
          : F.map p = F.map (Quiver.Hom.toPath Arrow.g) := by
        match p with
        | .cons tail Arrow.g =>
          match tail with
          | .nil =>
            rfl
          | .cons tail' Arrow.f =>
            change F.map ((Quiver.Hom.toPath Arrow.g ⊚
                           Quiver.Hom.toPath Arrow.f) ⊚ tail') = _
            rw [Functor.map_comp, h₁, Category.comp_id]
            exact aux₂₁ tail'
      intro p
      exact aux₂₁ p
```

```savedLean -show
end Ex17_2
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "203")
```savedComment
Exercise 17.3 (p. 203)
```

```savedLean -show
namespace Ex17_3
```

In the diagram

```savedLean
inductive Vertex
  | A | B | C | D | E | F | G | H

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .B .C
  | h : Edge .C .D
  | i : Edge .A .E
  | j : Edge .B .F
  | k : Edge .C .G
  | l : Edge .D .H
  | m : Edge .E .F
  | n : Edge .F .G
  | p : Edge .G .H

instance : Quiver Vertex where
  Hom := Edge
```

the three equations (1) $`{jf = mi}`, (2) $`{kg = nj}`, (3) $`{lh = pk}` actually force the diagram to commute; but you are just asked to prove that
$$`pnmi = lhgf`
:::

:::solution (solutionTo := "Exercise 3")
We can prove this directly in the free category on the graph using only the associative property of path composition.

```savedLean
open Edge Quiver Quiver.Hom Quiver.Path Vertex in
example
    (h₁ : (toPath f |>.comp (toPath j)) =
          (toPath i |>.comp (toPath m) : Path A F))
    (h₂ : (toPath g |>.comp (toPath k)) =
          (toPath j |>.comp (toPath n) : Path B G))
    (h₃ : (toPath h |>.comp (toPath l)) =
          (toPath k |>.comp (toPath p) : Path C H))
    : (toPath i
          |>.comp (toPath m)
          |>.comp (toPath n)
          |>.comp (toPath p)) =
      (toPath f
          |>.comp (toPath g)
          |>.comp (toPath h)
          |>.comp (Hom.toPath l) : Path A H) := by
  rw [comp_assoc, ← h₁]
  rw [← comp_assoc, comp_assoc (a := A) (toPath f), ← h₂]
  rw [comp_assoc, comp_assoc, ← h₃]
  repeat rw [← comp_assoc]
```

```savedLean -show
end Ex17_3
```
:::

:::question (questionTitle := "Exercise 4") (questionPage := "203")
For each of these diagrams, find a shortest list of equations that will make it commute.

...

After you have found the answers try to explain clearly how you know, from the equations you chose, that _all_ possible paths give equal composites.
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise 17.4 (p. 203)
```

\(a\) A shortest list of equations that will make diagram (a) commute is:
$$`gf = 1_A, \quad fg = 1_B, \quad g = h`

(cf. Exercise 2 above.)

```savedLean -show
namespace Ex17_4_a
```

```savedLean
inductive Vertex
  | A | B

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .B .A
  | h : Edge .B .A

instance : Quiver Vertex where
  Hom := Edge

example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :

    -- Let A' be the object in 𝒞 associated with Vertex.A in 𝐹(G)
    let A' : 𝒞 := F.obj Vertex.A
    -- Let B' be the object in 𝒞 associated with Vertex.B in 𝐹(G)
    let B' : 𝒞 := F.obj Vertex.B
    -- Let f' be the morphism in 𝒞 associated with Edge.f in 𝐹(G)
    let f' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.f)
    -- Let g' be the morphism in 𝒞 associated with Edge.g in 𝐹(G)
    let g' : B' ⟶ A' := F.map (Quiver.Hom.toPath Edge.g)
    -- Let h' be the morphism in 𝒞 associated with Edge.h in 𝐹(G)
    let h' : B' ⟶ A' := F.map (Quiver.Hom.toPath Edge.h)

    -- The 3 equations required to make the diagram commute
    g' ⊚ f' = 𝟙 A' ∧
    f' ⊚ g' = 𝟙 B' ∧
    g' = h' →
    -- .A ⟶ .A is interpreted as the identity on A' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A') ∧
    -- .B ⟶ .B is interpreted as the identity on B' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B') ∧
    -- .A ⟶ .B is interpreted as f' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = f') ∧
    -- .B ⟶ .A is interpreted as g' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = g') := by

  intro A' B' f' g' h' ⟨h₁, h₂, h₃⟩
  dsimp [A', B', f', g', h'] at h₁ h₂ h₃
  rw [← F.map_comp] at h₁ h₂
  and_intros
  -- ∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A'
  · let rec auxAA (p : Quiver.Path Vertex.A Vertex.A)
        : F.map p = 𝟙 (F.obj Vertex.A) := by
      match p with
      | .nil =>
        exact F.map_id _
      | .cons (.cons tail Edge.f) (e : Vertex.B ⟶ Vertex.A) =>
        have : F.map ((tail.cons Edge.f).cons e) =
               F.map ((Quiver.Hom.toPath Edge.g ⊚
                       Quiver.Hom.toPath Edge.f) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map (Quiver.Hom.toPath Edge.h ⊚
                          Quiver.Hom.toPath Edge.f ⊚ tail) = _
            rw [Functor.map_comp, ← h₃, ← Functor.map_comp,
                Category.assoc]
        rw [this]
        rw [Functor.map_comp, h₁, Category.comp_id]
        exact auxAA tail
    intro p
    exact auxAA p
  -- ∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B'
  · let rec auxBB (p : Quiver.Path Vertex.B Vertex.B)
        : F.map p = 𝟙 (F.obj Vertex.B) := by
      match p with
      | .nil =>
        exact F.map_id _
      | .cons (.cons tail (e : Vertex.B ⟶ Vertex.A)) Edge.f =>
        have : F.map ((tail.cons e).cons Edge.f) =
               F.map ((Quiver.Hom.toPath Edge.f ⊚
                       Quiver.Hom.toPath Edge.g) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map (Quiver.Hom.toPath Edge.f ⊚
                          Quiver.Hom.toPath Edge.h ⊚ tail) = _
            rw [Functor.map_comp, Functor.map_comp, ← h₃,
                ← Functor.map_comp, ← Functor.map_comp,
                Category.assoc]
        rw [this]
        rw [Functor.map_comp, h₂, Category.comp_id]
        exact auxBB tail
    intro p
    exact auxBB p
  -- ∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = f'
  · let rec auxAB (p : Quiver.Path Vertex.A Vertex.B)
        : F.map p = F.map (Quiver.Hom.toPath Edge.f) := by
      match p with
      | .cons .nil Edge.f =>
        rfl
      | .cons (.cons tail (e : Vertex.B ⟶ Vertex.A)) Edge.f =>
        have : F.map ((tail.cons e).cons Edge.f) =
               F.map ((Quiver.Hom.toPath Edge.f ⊚
                       Quiver.Hom.toPath Edge.g) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map ((Quiver.Hom.toPath Edge.f ⊚
                           Quiver.Hom.toPath Edge.h) ⊚ tail) = _
            rw [Functor.map_comp, Functor.map_comp, ← h₃,
                ← Functor.map_comp, ← Functor.map_comp]
        rw [this]
        rw [Functor.map_comp, h₂, Category.comp_id]
        exact auxAB tail
    intro p
    exact auxAB p
  -- ∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = g'
  · let rec auxBA (p : Quiver.Path Vertex.B Vertex.A)
        : F.map p = F.map (Quiver.Hom.toPath Edge.g) := by
      match p with
      | .cons .nil (e : Vertex.B ⟶ Vertex.A) =>
        rcases e
        · rfl
        · rw [h₃]
          rfl
      | .cons (.cons tail Edge.f) (e : Vertex.B ⟶ Vertex.A) =>
        have : F.map ((tail.cons Edge.f).cons e) =
               F.map ((Quiver.Hom.toPath Edge.g ⊚
                       Quiver.Hom.toPath Edge.f) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map ((Quiver.Hom.toPath Edge.h ⊚
                           Quiver.Hom.toPath Edge.f) ⊚ tail) = _
            rw [Functor.map_comp, Functor.map_comp, ← h₃,
                ← Functor.map_comp, ← Functor.map_comp]
        rw [this]
        rw [Functor.map_comp, h₁, Category.comp_id]
        exact auxBA tail
    intro p
    exact auxBA p
```

```savedLean -show
end Ex17_4_a
```

\(b\) A shortest list of equations that will make diagram (b) commute is:
$$`hgf = 1_A, \quad fhg = 1_B, \quad gfh = 1_C`

Since there are now nine possible pairings of dots, we change our approach from Exercises 2 and 4(a) above and instead employ a more efficient proof by induction.

```savedLean -show
namespace Ex17_4_b
```

```savedLean
inductive Vertex
  | A | B | C

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .B .C
  | h : Edge .C .A

instance : Quiver Vertex where
  Hom := Edge

example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :

    -- Let A' be the object in 𝒞 associated with Vertex.A in 𝐹(G)
    let A' : 𝒞 := F.obj Vertex.A
    -- Let B' be the object in 𝒞 associated with Vertex.B in 𝐹(G)
    let B' : 𝒞 := F.obj Vertex.B
    -- Let C' be the object in 𝒞 associated with Vertex.C in 𝐹(G)
    let C' : 𝒞 := F.obj Vertex.C
    -- Let f' be the morphism in 𝒞 associated with Edge.f in 𝐹(G)
    let f' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.f)
    -- Let g' be the morphism in 𝒞 associated with Edge.g in 𝐹(G)
    let g' : B' ⟶ C' := F.map (Quiver.Hom.toPath Edge.g)
    -- Let h' be the morphism in 𝒞 associated with Edge.h in 𝐹(G)
    let h' : C' ⟶ A' := F.map (Quiver.Hom.toPath Edge.h)

    -- The 3 equations required to make the diagram commute
    h' ⊚ g' ⊚ f' = 𝟙 A' ∧
    f' ⊚ h' ⊚ g' = 𝟙 B' ∧
    g' ⊚ f' ⊚ h' = 𝟙 C' →
    -- .A ⟶ .A is interpreted as the identity on A' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A') ∧
    -- .B ⟶ .B is interpreted as the identity on B' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B') ∧
    -- .C ⟶ .C is interpreted as the identity on C' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.C, F.map p = 𝟙 C') ∧
    -- .A ⟶ .B is interpreted as f' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = f') ∧
    -- .B ⟶ .C is interpreted as g' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.C, F.map p = g') ∧
    -- .C ⟶ .A is interpreted as h' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.A, F.map p = h') ∧
    -- .A ⟶ .C is interpreted as g' ⊚ f' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.C, F.map p = g' ⊚ f') ∧
    -- .B ⟶ .A is interpreted as h' ⊚ g' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = h' ⊚ g') ∧
    -- .C ⟶ .B is interpreted as f' ⊚ h' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.B, F.map p = f' ⊚ h') := by

  intro A' B' C' f' g' h' ⟨h₁, h₂, h₃⟩
  suffices ∀ {u v : Vertex} (p : Quiver.Path u v), F.map p =
    match u, v with
    | .A, .A => 𝟙 A'
    | .B, .B => 𝟙 B'
    | .C, .C => 𝟙 C'
    | .A, .B => f'
    | .B, .C => g'
    | .C, .A => h'
    | .A, .C => g' ⊚ f'
    | .B, .A => h' ⊚ g'
    | .C, .B => f' ⊚ h' by
    simp [this]
  dsimp [A', B', C', f', g', h'] at h₁ h₂ h₃
  intro u v p
  induction p with
  | nil =>
    cases u
    all_goals
      dsimp
      exact F.map_id _
  | cons p e ih =>
    change F.map (Quiver.Hom.toPath e ⊚ p) = _
    rw [F.map_comp, ih]
    cases u <;> rcases e
    all_goals
      dsimp [A', B', C', f', g', h']
      try rw [Category.id_comp]
      try first | rw [h₁] | rw [h₂] | rw [h₃]
```

```savedLean -show
end Ex17_4_b
```

\(c\) A shortest list of equations that will make diagram (c) commute is:
$$`jhg = 1_A, \quad gjh = 1_B, \quad hgj = 1_C, \quad f = g, \quad i = 1_C`

```savedLean -show
namespace Ex17_4_c
```

```savedLean
inductive Vertex
  | A | B | C

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .A .B
  | h : Edge .B .C
  | i : Edge .C .C
  | j : Edge .C .A

instance : Quiver Vertex where
  Hom := Edge

example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :

    -- Let A' be the object in 𝒞 associated with Vertex.A in 𝐹(G)
    let A' : 𝒞 := F.obj Vertex.A
    -- Let B' be the object in 𝒞 associated with Vertex.B in 𝐹(G)
    let B' : 𝒞 := F.obj Vertex.B
    -- Let C' be the object in 𝒞 associated with Vertex.C in 𝐹(G)
    let C' : 𝒞 := F.obj Vertex.C
    -- Let f' be the morphism in 𝒞 associated with Edge.f in 𝐹(G)
    let f' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.f)
    -- Let g' be the morphism in 𝒞 associated with Edge.g in 𝐹(G)
    let g' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.g)
    -- Let h' be the morphism in 𝒞 associated with Edge.h in 𝐹(G)
    let h' : B' ⟶ C' := F.map (Quiver.Hom.toPath Edge.h)
    -- Let i' be the morphism in 𝒞 associated with Edge.i in 𝐹(G)
    let i' : C' ⟶ C' := F.map (Quiver.Hom.toPath Edge.i)
    -- Let j' be the morphism in 𝒞 associated with Edge.j in 𝐹(G)
    let j' : C' ⟶ A' := F.map (Quiver.Hom.toPath Edge.j)

    -- The 5 equations required to make the diagram commute
    j' ⊚ h' ⊚ g' = 𝟙 A' ∧
    g' ⊚ j' ⊚ h' = 𝟙 B' ∧
    h' ⊚ g' ⊚ j' = 𝟙 C' ∧
    f' = g' ∧
    i' = 𝟙 C' →
    -- .A ⟶ .A is interpreted as the identity on A' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A') ∧
    -- .B ⟶ .B is interpreted as the identity on B' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B') ∧
    -- .C ⟶ .C is interpreted as the identity on C' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.C, F.map p = 𝟙 C') ∧
    -- .A ⟶ .B is interpreted as g' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = g') ∧
    -- .B ⟶ .C is interpreted as h' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.C, F.map p = h') ∧
    -- .C ⟶ .A is interpreted as j' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.A, F.map p = j') ∧
    -- .A ⟶ .C is interpreted as h' ⊚ g' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.C, F.map p = h' ⊚ g') ∧
    -- .B ⟶ .A is interpreted as j' ⊚ h' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = j' ⊚ h') ∧
    -- .C ⟶ .B is interpreted as g' ⊚ j' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.B, F.map p = g' ⊚ j') := by

  intro A' B' C' f' g' h' i' j' ⟨h₁, h₂, h₃, h₄, h₅⟩
  suffices ∀ {u v : Vertex} (p : Quiver.Path u v), F.map p =
    match u, v with
    | .A, .A => 𝟙 A'
    | .B, .B => 𝟙 B'
    | .C, .C => 𝟙 C'
    | .A, .B => g'
    | .B, .C => h'
    | .C, .A => j'
    | .A, .C => h' ⊚ g'
    | .B, .A => j' ⊚ h'
    | .C, .B => g' ⊚ j' by
    simp [this]
  dsimp [A', B', C', f', g', h', i', j'] at h₁ h₂ h₃ h₄ h₅
  intro u v p
  induction p with
  | nil =>
    cases u
    all_goals
      dsimp
      exact F.map_id _
  | cons p e ih =>
    change F.map (Quiver.Hom.toPath e ⊚ p) = _
    rw [F.map_comp, ih]
    cases u <;> rcases e
    all_goals
      dsimp [A', B', C', f', g', h', i', j']
      try rw [h₄]
      try rw [h₅]
      try first | rw [Category.comp_id] | rw [Category.id_comp]
      try first | rw [h₁] | rw [h₂] | rw [h₃]
```

```savedLean -show
end Ex17_4_c
```
:::

```savedLean -show
end CM
```
