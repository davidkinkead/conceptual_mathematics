import ConceptualMathematics.Article2
import ConceptualMathematics.Review
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
The (concrete) category 𝑺↻ of endomaps of sets (pp. 136–137)
-/
structure SetWithEndomap where
  t : Type
  carrier : Set t
  toEnd : t ⟶ t
  toEnd_mem {a} : a ∈ carrier → toEnd a ∈ carrier

def SetWithEndomapHom (X Y : SetWithEndomap) := {
  f : X.t ⟶ Y.t //
      (∀ x ∈ X.carrier, f x ∈ Y.carrier) -- maps to codomain
      ∧ f ⊚ X.toEnd = Y.toEnd ⊚ f -- commutes
}

def SetWithEndomapHom.id (X : SetWithEndomap)
    : SetWithEndomapHom X X := ⟨
  𝟙 X.t,
  by
    constructor
    · intro _ hx
      exact hx
    · rfl
⟩

def SetWithEndomapHom.comp {X Y Z : SetWithEndomap}
    (f : SetWithEndomapHom X Y) (g : SetWithEndomapHom Y Z)
    : SetWithEndomapHom X Z := ⟨
  g.val ⊚ f.val,
  by
    obtain ⟨hf_mtc, hf_comm⟩ := f.property
    obtain ⟨hg_mtc, hg_comm⟩ := g.property
    constructor
    · intro x hx
      exact hg_mtc (f.val x) (hf_mtc x hx)
    · rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
          ← Category.assoc]
⟩

instance instCatSetWithEndomap : Category SetWithEndomap where
  Hom := SetWithEndomapHom
  id := SetWithEndomapHom.id
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithEndomap}
    : FunLike (instCatSetWithEndomap.Hom X Y) X.t Y.t where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance
    : ConcreteCategory SetWithEndomap instCatSetWithEndomap.Hom where
  hom f := f
  ofHom f := f

/-!
Exercise III.1 (p. 137)
-/
example {X Y Z : Type}
    (α : X ⟶ X) (β : Y ⟶ Y) (γ : Z ⟶ Z)
    (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)
    (g : Y ⟶ Z) (hg_comm : g ⊚ β = γ ⊚ g)
    : (g ⊚ f) ⊚ α = γ ⊚ (g ⊚ f) := by
  -- cf. SetWithEndomapHom.comp above
  rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
      ← Category.assoc]

example {X Y Z : SetWithEndomap} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z :=
  g ⊚ f

/-!
The (concrete) category 𝑺ᵉ of idempotent endomaps of sets (p. 138)
-/
structure SetWithIdemEndomap extends SetWithEndomap where
  idem : toEnd ⊚ toEnd = toEnd

instance instCatSetWithIdemEndomap : Category SetWithIdemEndomap where
  Hom X Y := SetWithEndomapHom X.toSetWithEndomap Y.toSetWithEndomap
  id X := SetWithEndomapHom.id X.toSetWithEndomap
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithIdemEndomap}
    : FunLike (instCatSetWithIdemEndomap.Hom X Y) X.t Y.t where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance
    : ConcreteCategory SetWithIdemEndomap instCatSetWithIdemEndomap.Hom
    where
  hom f := f
  ofHom f := f

/-!
The (concrete) category 𝑺◯ of invertible endomaps of sets (p. 138)
-/
structure SetWithInvEndomap extends SetWithEndomap where
  inv : ∃ inv, inv ⊚ toEnd = 𝟙 t ∧ toEnd ⊚ inv = 𝟙 t

instance instCatSetWithInvEndomap : Category SetWithInvEndomap where
  Hom X Y := SetWithEndomapHom X.toSetWithEndomap Y.toSetWithEndomap
  id X := SetWithEndomapHom.id X.toSetWithEndomap
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithInvEndomap}
    : FunLike (instCatSetWithInvEndomap.Hom X Y) X.t Y.t where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance
    : ConcreteCategory SetWithInvEndomap instCatSetWithInvEndomap.Hom
    where
  hom f := f
  ofHom f := f

/-!
The (concrete) category 𝑪↻ of endomaps (pp. 138–139)
-/
structure Endomap where
  carrier : Type
  toEnd : carrier ⟶ carrier

def EndomapHom (X Y : Endomap) := {
  f : X.carrier ⟶ Y.carrier //
      f ⊚ X.toEnd = Y.toEnd ⊚ f -- commutes
}

namespace EndomapHom

def id (X : Endomap) : EndomapHom X X := ⟨
  𝟙 X.carrier,
  rfl
⟩

def comp {X Y Z : Endomap}
    (f : EndomapHom X Y) (g : EndomapHom Y Z)
    : EndomapHom X Z := ⟨
  g.val ⊚ f.val,
  by
    obtain hf_comm := f.property
    obtain hg_comm := g.property
    rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
        ← Category.assoc]
⟩

end EndomapHom

instance instCatEndomap : Category Endomap where
  Hom := EndomapHom
  id := EndomapHom.id
  comp := EndomapHom.comp

instance {X Y : Endomap}
    : FunLike (instCatEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory Endomap instCatEndomap.Hom where
  hom f := f
  ofHom f := f

/-!
The (concrete) category 𝑪ᵉ of idempotents (pp. 138–139)
-/
structure IdemEndomap extends Endomap where
  idem : toEnd ⊚ toEnd = toEnd

instance instCatIdemEndomap : Category IdemEndomap where
  Hom X Y := EndomapHom X.toEndomap Y.toEndomap
  id X := EndomapHom.id X.toEndomap
  comp := EndomapHom.comp

instance {X Y : IdemEndomap}
    : FunLike (instCatIdemEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory IdemEndomap instCatIdemEndomap.Hom where
  hom f := f
  ofHom f := f

/-!
The (concrete) category 𝑪◯ of isomorphic endomaps (pp. 138–139)
-/
structure InvEndomap extends Endomap where
  inv : ∃ inv, inv ⊚ toEnd = 𝟙 carrier ∧ toEnd ⊚ inv = 𝟙 carrier

instance instCatInvEndomap : Category InvEndomap where
  Hom X Y := EndomapHom X.toEndomap Y.toEndomap
  id X := EndomapHom.id X.toEndomap
  comp := EndomapHom.comp

instance {X Y : InvEndomap}
    : FunLike (instCatInvEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory InvEndomap instCatInvEndomap.Hom where
  hom f := f
  ofHom f := f

/-!
The (concrete) category 𝑪ᶿ of involutions (pp. 138–139)
-/
structure InvolEndomap extends InvEndomap where
  invol : toEnd ⊚ toEnd = 𝟙 carrier

instance instCatInvolEndomap : Category InvolEndomap where
  Hom X Y := EndomapHom X.toEndomap Y.toEndomap
  id X := EndomapHom.id X.toEndomap
  comp := EndomapHom.comp

instance {X Y : InvolEndomap}
    : FunLike (instCatInvolEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory InvolEndomap instCatInvolEndomap.Hom where
  hom f := f
  ofHom f := f

/-!
Exercise III.2 (p. 139)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞} {α β : A ⟶ A}
    (h_idem : α ⊚ α = α) (h_retraction : β ⊚ α = 𝟙 A)
    : α = 𝟙 A := by
  calc
    α = 𝟙 A ⊚ α := by rw [Category.comp_id]
    _ = (β ⊚ α) ⊚ α := by rw [h_retraction]
    _ = β ⊚ α ⊚ α := by rw [Category.assoc]
    _ = β ⊚ α := by rw [h_idem]
    _ = 𝟙 A := by rw [h_retraction]

/-!
Exercise III.3 (p. 140)
-/
/-!
Exercise III.4 (p. 140)
-/
namespace ExIII_4

def α : ℤ ⟶ ℤ := fun x ↦ -x

example : ¬(IsIdempotent α) := by
  by_contra h
  have h_contra : (α ⊚ α) 1 = α 1 := congrFun h.idem 1
  dsimp [α] at h_contra
  contradiction

example : IsInvolution α := {
  invol := by
    funext
    dsimp [CategoryStruct.comp, α]
    ring
}

example {x : ℤ} : Function.IsFixedPt α x ↔ x = 0 := by
  dsimp [Function.IsFixedPt, α]
  constructor
  · exact eq_zero_of_neg_eq
  · intro hx
    rw [hx]
    exact neg_zero

theorem _root_.eq_zero_iff_neg_eq {α : Type u}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {a : α} : -a = a ↔ a = 0 := by
  constructor
  · exact eq_zero_of_neg_eq
  · intro h
    rw [h]
    exact neg_zero

example {x : ℤ} : Function.IsFixedPt α x ↔ x = 0 := eq_zero_iff_neg_eq

end ExIII_4

/-!
Exercise III.5 (p. 140)
-/
namespace ExIII_5

def α : ℤ ⟶ ℤ := fun x ↦ |x|

example : IsIdempotent α := {
  idem := by
    funext
    dsimp [CategoryStruct.comp, α]
    rw [abs_abs]
}

example : ¬(IsInvolution α) := by
  by_contra h
  have h_contra : (α ⊚ α) (-1) = (𝟙 ℤ) (-1) := congrFun h.invol (-1)
  dsimp [α] at h_contra
  contradiction

example {x : ℤ} : Function.IsFixedPt α x ↔ 0 ≤ x := by
  dsimp [Function.IsFixedPt, α]
  constructor
  · intro hx
    rw [← hx]
    exact abs_nonneg x
  · exact abs_of_nonneg

theorem _root_.abs_iff_nonneg {α : Type u_1}
    [Lattice α] [AddGroup α]
    {a : α} [AddLeftMono α] [AddRightMono α] : 0 ≤ a ↔ |a| = a := by
  constructor
  · exact abs_of_nonneg
  · intro h
    rw [← h]
    exact abs_nonneg a

example {x : ℤ} : Function.IsFixedPt α x ↔ 0 ≤ x := abs_iff_nonneg.symm

end ExIII_5

/-!
Exercise III.6 (p. 140)
-/
namespace ExIII_6

def α : ℤ ⟶ ℤ := fun x ↦ x + 3

example : IsIso α := by
  let αinv : ℤ ⟶ ℤ := fun x ↦ x - 3
  exact {
    out := by
      use αinv
      constructor
      all_goals
        funext
        dsimp [CategoryStruct.comp, α, αinv]
        ring
  }

end ExIII_6

/-!
Exercise III.7 (p. 140)
-/
namespace ExIII_7

def α : ℤ ⟶ ℤ := fun x ↦ 5 * x

example : ¬(IsIso α) := by
  by_contra h
  obtain ⟨αinv, _, h_right_inv⟩ := h.out
  have h_contra₁ : (α ⊚ αinv) 1 = (𝟙 ℤ) 1 := congrFun h_right_inv 1
  have h_contra₂ : (5 : ℤ) ∣ 1 := by
    use αinv 1
    exact h_contra₁.symm
  contradiction

end ExIII_7

/-!
Exercise III.8 (p. 140)
-/
example {α : IdemEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd := by
  repeat rw [α.idem]

example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsIdempotent α] : α ⊚ α ⊚ α = α := by
  repeat rw [IsIdempotent.idem]

example {α : InvolEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd := by
  rw [α.invol, Category.id_comp]

example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsInvolution α] : α ⊚ α ⊚ α = α := by
  rw [IsInvolution.invol, Category.id_comp]

/-!
Exercise III.9 (p. 141)
-/
namespace ExIII_9

inductive A
  | a₁ | a₂ | a₃

def α : A ⟶ A
  | A.a₁ => A.a₂
  | A.a₂ => A.a₃
  | A.a₃ => A.a₂

example : α ⊚ α ⊚ α = α := by
  funext x
  dsimp [CategoryStruct.comp, α]
  cases x <;> rfl

example : ¬(IsIdempotent α) := by
  by_contra h
  have h_contra : (α ⊚ α) A.a₁ = α A.a₁ := congrFun h.idem A.a₁
  dsimp [α] at h_contra
  contradiction

example : ¬(IsInvolution α) := by
  by_contra h
  have h_contra : (α ⊚ α) A.a₁ = (𝟙 A) A.a₁ := congrFun h.invol A.a₁
  dsimp [α] at h_contra
  contradiction

end ExIII_9

/-!
Exercise III.10 (p. 141)
-/
namespace ExIII_10

inductive X
  | a | b | c | d | e

inductive P
  | k | m | n | p | q | r

def s : X ⟶ P
    | X.a => P.k
    | X.b => P.m
    | X.c => P.k
    | X.d => P.p
    | X.e => P.m

def t : X ⟶ P
    | X.a => P.m
    | X.b => P.m
    | X.c => P.m
    | X.d => P.q
    | X.e => P.r

example : s X.b = t X.b := rfl

example : ¬(∃ x : X, t x = P.k) := by
  push_neg
  intro x
  cases x <;> simp [t]

end ExIII_10

/-!
The category 𝑺⇊ of (irreflexive directed multi-) graphs (pp. 141–142)
-/
structure IrreflexiveGraph where
  tA : Type
  carrierA : Set tA
  tD : Type
  carrierD : Set tD
  toSrc : tA ⟶ tD
  toSrc_mem {a} : a ∈ carrierA → toSrc a ∈ carrierD
  toTgt : tA ⟶ tD
  toTgt_mem {a} : a ∈ carrierA → toTgt a ∈ carrierD

instance instCategoryIrreflexiveGraph : Category IrreflexiveGraph where
  Hom X Y := {
    f : (X.tA ⟶ Y.tA) × (X.tD ⟶ Y.tD) //
        (∀ x ∈ X.carrierA, f.1 x ∈ Y.carrierA) -- fA maps to codomain
        ∧ (∀ x ∈ X.carrierD, f.2 x ∈ Y.carrierD) -- fD maps to codomain
        ∧ f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
  }
  id X := ⟨
    (𝟙 X.tA, 𝟙 X.tD),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfA_mtc, hfD_mtc, hfSrc_comm, hfTgt_comm⟩ := hf
        obtain ⟨hgA_mtc, hgD_mtc, hgSrc_comm, hgTgt_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgA_mtc (f.1 x) (hfA_mtc x hx)
        · intro x hx
          exact hgD_mtc (f.2 x) (hfD_mtc x hx)
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
              ← Category.assoc]
    ⟩

/-!
Exercise III.11 (p. 142)
-/
namespace ExIII_11

variable (X P Y Q Z R : Type)
         (s t : X ⟶ P) (s' t' : Y ⟶ Q) (s'' t'' : Z ⟶ R)

example (fA : X ⟶ Y) (fD : P ⟶ Q) (gA : Y ⟶ Z) (gD : Q ⟶ R)
    (hfSrc_comm : fD ⊚ s = s' ⊚ fA)
    (hfTgt_comm : fD ⊚ t = t' ⊚ fA)
    (hgSrc_comm : gD ⊚ s' = s'' ⊚ gA)
    (hgTgt_comm : gD ⊚ t' = t'' ⊚ gA)
    : (gD ⊚ fD) ⊚ s = s'' ⊚ (gA ⊚ fA)
        ∧ (gD ⊚ fD) ⊚ t = t'' ⊚ (gA ⊚ fA)
    := by
  constructor
  -- cf. instCategoryIrreflexiveGraph.comp above
  · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
        ← Category.assoc]
  · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
        ← Category.assoc]

def graph (A D : Type) (src tgt : A ⟶ D) : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := src
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := tgt
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

example (f : graph X P s t ⟶ graph Y Q s' t')
    (g : graph Y Q s' t' ⟶ graph Z R s'' t'')
    : graph X P s t ⟶ graph Z R s'' t'' := g ⊚ f

end ExIII_11

/-!
Exercise III.12 (p. 143)
-/
def functorSetWithEndomapToIrreflexiveGraph
    : Functor SetWithEndomap IrreflexiveGraph := {
  obj (X : SetWithEndomap) := {
    tA := X.t
    carrierA := Set.univ
    tD := X.t
    carrierD := Set.univ
    toSrc := 𝟙 X.t
    toSrc_mem := fun _ ↦ Set.mem_univ _
    toTgt := X.toEnd
    toTgt_mem := fun _ ↦ Set.mem_univ _
  }
  map {X Y : SetWithEndomap} (f : X ⟶ Y) := {
    val := (f, f)
    property := by
      obtain ⟨tX, carrierX, toEndX⟩ := X
      obtain ⟨tY, carrierY, toEndY⟩ := Y
      obtain ⟨f, hf_mtc, hf_comm⟩ := f
      dsimp at f hf_mtc hf_comm
      split_ands <;> (dsimp; intros; trivial)
  }
}

-- Helper function to align to the notation in the book
def I {X Y : SetWithEndomap} (f : X ⟶ Y) :=
  functorSetWithEndomapToIrreflexiveGraph.map f

example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : I (g ⊚ f) = I g ⊚ I f := rfl

/-!
Exercise III.13 (p. 144)
-/
namespace ExIII_13

variable (X' Y' : SetWithEndomap)

def graph₁ (S : SetWithEndomap) : IrreflexiveGraph := {
  tA := S.t
  carrierA := Set.univ
  tD := S.t
  carrierD := Set.univ
  toSrc := 𝟙 S.t
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := S.toEnd
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

variable (f₁ : graph₁ X' ⟶ graph₁ Y')

-- Align to the notation in the book: fA is f₁.val.1, fD is f₁.val.2
set_option quotPrecheck false
local notation "fA₁" => f₁.val.1
local notation "fD₁" => f₁.val.2
set_option quotPrecheck true

example : fA₁ = fD₁ := by
  obtain ⟨_, _ , hfSrc_comm, _⟩ := f₁.property
  dsimp [graph₁] at hfSrc_comm
  exact hfSrc_comm.symm

def graph₂ (S : SetWithEndomap) : IrreflexiveGraph :=
  functorSetWithEndomapToIrreflexiveGraph.obj S

variable (f₂ : graph₂ X' ⟶ graph₂ Y')

set_option quotPrecheck false
local notation "fA₂" => f₂.val.1
local notation "fD₂" => f₂.val.2
set_option quotPrecheck true

example : fA₂ = fD₂ := by
  obtain ⟨_, _ , hfSrc_comm, _⟩ := f₂.property
  dsimp [graph₂, functorSetWithEndomapToIrreflexiveGraph]
      at hfSrc_comm
  exact hfSrc_comm.symm

end ExIII_13

/-!
The category 𝑺↓ of simple directed graphs (pp. 144–145)
-/
structure SimpleGraph where
  tA : Type
  carrierA : Set tA
  tD : Type
  carrierD : Set tD
  toFun : tA ⟶ tD
  toFun_mem {a} : a ∈ carrierA → toFun a ∈ carrierD

instance : Category SimpleGraph where
  Hom X Y := {
    f : (X.tA ⟶ Y.tA) × (X.tD ⟶ Y.tD) //
        (∀ x ∈ X.carrierA, f.1 x ∈ Y.carrierA) -- fA maps to codomain
        ∧ (∀ x ∈ X.carrierD, f.2 x ∈ Y.carrierD) -- fD maps to codomain
        ∧ f.2 ⊚ X.toFun = Y.toFun ⊚ f.1 -- commutes
  }
  id X := ⟨
    (𝟙 X.tA, 𝟙 X.tD),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfA_mtc, hfD_mtc, hfSrc_comm⟩ := hf
        obtain ⟨hgA_mtc, hgD_mtc, hgSrc_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgA_mtc (f.1 x) (hfA_mtc x hx)
        · intro x hx
          exact hgD_mtc (f.2 x) (hfD_mtc x hx)
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
    ⟩

def functorSetWithEndomapToSimpleGraph
    : Functor SetWithEndomap SimpleGraph := {
  obj (X : SetWithEndomap) := {
    tA := X.t
    carrierA := Set.univ
    tD := X.t
    carrierD := Set.univ
    toFun := X.toEnd
    toFun_mem := fun _ ↦ Set.mem_univ _
  }
  map {X Y : SetWithEndomap} (f : X ⟶ Y) := {
    val := (f, f)
    property := by
      obtain ⟨tX, carrierX, toEndX⟩ := X
      obtain ⟨tY, carrierY, toEndY⟩ := Y
      obtain ⟨f, hf_mtc, hf_comm⟩ := f
      dsimp at f hf_mtc hf_comm
      split_ands <;> (dsimp; intros; trivial)
  }
}

-- Helper function to align to the notation in the book
def J {X Y : SetWithEndomap} (f : X ⟶ Y) :=
  functorSetWithEndomapToSimpleGraph.map f

example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : J (g ⊚ f) = J g ⊚ J f := rfl

/-!
Exercise III.14 (p. 144)
-/
namespace ExIII_14

inductive X
  | x₁ | x₂

inductive Y
  | y₁ | y₂

def α : X ⟶ X
  | X.x₁ => X.x₁
  | X.x₂ => X.x₁

def β : Y ⟶ Y
  | Y.y₁ => Y.y₁
  | Y.y₂ => Y.y₁

def fA : X ⟶ Y
  | X.x₁ => Y.y₁
  | X.x₂ => Y.y₂

def fD : X ⟶ Y
  | X.x₁ => Y.y₁
  | X.x₂ => Y.y₁

example : fD ⊚ α = β ⊚ fA ∧ fA ≠ fD := by
  constructor
  · funext x
    cases x <;> rfl
  · by_contra h
    have h_contra : fA X.x₂ = fD X.x₂ := congrFun h X.x₂
    dsimp [fA, fD] at h_contra
    contradiction

end ExIII_14

/-!
The category of reflexive graphs (p. 145)
-/
structure ReflexiveGraph extends IrreflexiveGraph where
  toCommonSection : tD ⟶ tA
  toCommonSection_mem {d} : d ∈ carrierD → toCommonSection d ∈ carrierA
  section_src : toSrc ⊚ toCommonSection = 𝟙 tD
  section_tgt : toTgt ⊚ toCommonSection = 𝟙 tD

instance : Category ReflexiveGraph where
  Hom X Y := {
    f : (X.tA ⟶ Y.tA) × (X.tD ⟶ Y.tD) //
        (∀ x ∈ X.carrierA, f.1 x ∈ Y.carrierA) -- fA maps to codomain
        ∧ (∀ x ∈ X.carrierD, f.2 x ∈ Y.carrierD) -- fD maps to codomain
        ∧ f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
        ∧ f.1 ⊚ X.toCommonSection = Y.toCommonSection ⊚ f.2
  }
  id X := ⟨
    (𝟙 X.tA, 𝟙 X.tD),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfA_mtc, hfD_mtc, hfSrc_comm, hfTgt_comm,
            hfCommonSection_comm⟩ := hf
        obtain ⟨hgA_mtc, hgD_mtc, hgSrc_comm, hgTgt_comm,
            hgCommonSection_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgA_mtc (f.1 x) (hfA_mtc x hx)
        · intro x hx
          exact hgD_mtc (f.2 x) (hfD_mtc x hx)
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfCommonSection_comm, Category.assoc,
              hgCommonSection_comm, ← Category.assoc]
    ⟩

/-!
Exercise III.15 (p. 145)
-/
namespace ExIII_15

variable (X : ReflexiveGraph)

variable (e₁ e₀ : X.tA ⟶ X.tA)
         (h₁ : e₁ = X.toCommonSection ⊚ X.toSrc)
         (h₀ : e₀ = X.toCommonSection ⊚ X.toTgt)

example : e₀ ⊚ e₀ = e₀ := by
  rw [h₀, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_tgt, Category.id_comp]

example : e₀ ⊚ e₁ = e₁ := by
  rw [h₀, h₁, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_tgt, Category.id_comp]

example : e₁ ⊚ e₀ = e₀ := by
  rw [h₁, h₀, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_src, Category.id_comp]

example : e₁ ⊚ e₁ = e₁ := by
  rw [h₁, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_src, Category.id_comp]

end ExIII_15

/-!
Exercise III.16 (p. 145)
-/
namespace ExIII_16

variable (X Y : ReflexiveGraph) (f : X ⟶ Y)

-- Align to the notation in the book
set_option quotPrecheck false
local notation "fA" => f.val.1
local notation "fD" => f.val.2
set_option quotPrecheck true

local notation "s" => X.toSrc
local notation "s'" => Y.toSrc
local notation "t" => X.toTgt
local notation "t'" => Y.toTgt
local notation "i" => X.toCommonSection
local notation "i'" => Y.toCommonSection

example : fD = s' ⊚ fA ⊚ i := by
  rw [← Category.id_comp fD, ← X.section_src]
  repeat rw [Category.assoc]
  congrm ?_ ⊚ X.toCommonSection
  exact f.property.2.2.1

example : fD = t' ⊚ fA ⊚ i := by
  rw [← Category.id_comp fD, ← X.section_tgt]
  repeat rw [Category.assoc]
  congrm ?_ ⊚ X.toCommonSection
  exact f.property.2.2.2.1

end ExIII_16

/-!
Exercise III.17 (p. 145)
-/
namespace ExIII_17

structure ParentLike where
  tM : Type
  carrierM : Set tM
  tF : Type
  carrierF : Set tF
  φ : tM ⟶ tM
  φ_mem {m} : m ∈ carrierM → φ m ∈ carrierM
  φ' : tF ⟶ tM
  φ'_mem {f} : f ∈ carrierF → φ' f ∈ carrierM
  μ : tF ⟶ tF
  μ_mem {f} : f ∈ carrierF → μ f ∈ carrierF
  μ' : tM ⟶ tF
  μ'_mem {m} : m ∈ carrierM → μ' m ∈ carrierF

def ParentLikeHom (X Y : ParentLike) := {
  f : (X.tM ⟶ Y.tM) × (X.tF ⟶ Y.tF) //
      (∀ x ∈ X.carrierM, f.1 x ∈ Y.carrierM) -- f.1 maps to codomain
      ∧ (∀ x ∈ X.carrierF, f.2 x ∈ Y.carrierF) -- f.2 maps to codomain
      ∧ f.1 ⊚ X.φ = Y.φ ⊚ f.1 -- φ commutes
      ∧ f.1 ⊚ X.φ' = Y.φ' ⊚ f.2 -- φ' commutes
      ∧ f.2 ⊚ X.μ = Y.μ ⊚ f.2 -- μ commutes
      ∧ f.2 ⊚ X.μ' = Y.μ' ⊚ f.1 -- μ' commutes
}

instance : Category ParentLike where
  Hom := ParentLikeHom -- our map between ParentLike structures
  id X := ⟨
    (𝟙 X.tM, 𝟙 X.tF),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfM_mtc, hfF_mtc, hfφ_comm, hfφ'_comm, hfμ_comm,
            hfμ'_comm⟩ := hf
        obtain ⟨hgM_mtc, hgF_mtc, hgφ_comm, hgφ'_comm, hgμ_comm,
            hgμ'_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgM_mtc (f.1 x) (hfM_mtc x hx)
        · intro x hx
          exact hgF_mtc (f.2 x) (hfF_mtc x hx)
        · rw [← Category.assoc, hfφ_comm, Category.assoc, hgφ_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfφ'_comm, Category.assoc, hgφ'_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfμ_comm, Category.assoc, hgμ_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfμ'_comm, Category.assoc, hgμ'_comm,
              ← Category.assoc]
    ⟩

end ExIII_17

/-!
Exercise III.18 (p. 146)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y T : 𝒞}
    {a : X ⟶ Y} {p : Y ⟶ X} {x₁ x₂ : T ⟶ X}
    (h₁ : p ⊚ a = 𝟙 X) (h₂ : a ⊚ x₁ = a ⊚ x₂)
    : x₁ = x₂ := by
  calc x₁
    _ = 𝟙 X ⊚ x₁ := by rw [Category.comp_id]
    _ = (p ⊚ a) ⊚ x₁ := by rw [h₁]
    _ = p ⊚ a ⊚ x₁ := by rw [Category.assoc]
    _ = p ⊚ a ⊚ x₂ := by rw [h₂]
    _ = (p ⊚ a) ⊚ x₂ := by rw [Category.assoc]
    _ = 𝟙 X ⊚ x₂ := by rw [h₁]
    _ = x₂ := by rw [Category.comp_id]

namespace ExIII_19_24

inductive X
  | x₀ | x₁
  deriving Fintype

inductive Y
  | y₀ | y₁ | y₂
  deriving Fintype

def α : X ⟶ X
  | X.x₀ => X.x₀
  | X.x₁ => X.x₀

def β : Y ⟶ Y
  | Y.y₀ => Y.y₀
  | Y.y₁ => Y.y₀
  | Y.y₂ => Y.y₁

def a : X ⟶ Y
  | X.x₀ => Y.y₀
  | X.x₁ => Y.y₁

/-!
Exercise III.19 (p. 147)
-/
example : a ⊚ α = β ⊚ a := by
  funext x
  cases x <;> rfl

def Xα : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def Yβ : SetWithEndomap := {
  t := Y
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def a' : Xα ⟶ Yβ := ⟨
  a,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

/-!
Exercise III.20 (p. 147)
-/
example : ∀ {T : Type} (x₁ x₂ : T ⟶ X),
    a ⊚ x₁ = a ⊚ x₂ → x₁ = x₂ := by
  let p : Y ⟶ X
    | Y.y₀ => X.x₀
    | Y.y₁ => X.x₁
    | Y.y₂ => X.x₁
  have h₁ : p ⊚ a = 𝟙 X := by
    funext x
    cases x <;> rfl
  intro _ x₁ x₂ h₂
  calc x₁
    _ = 𝟙 X ⊚ x₁ := by rw [Category.comp_id]
    _ = (p ⊚ a) ⊚ x₁ := by rw [h₁]
    _ = p ⊚ a ⊚ x₁ := by rw [Category.assoc]
    _ = p ⊚ a ⊚ x₂ := by rw [h₂]
    _ = (p ⊚ a) ⊚ x₂ := by rw [Category.assoc]
    _ = 𝟙 X ⊚ x₂ := by rw [h₁]
    _ = x₂ := by rw [Category.comp_id]

/-!
Exercise III.21 (p. 147)
-/
def p₁ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : p₁ ⊚ a = 𝟙 X := by
  funext x
  cases x <;> rfl

#eval Danilo's_formula (Finset.univ) (Finset.univ) a p₁
  (by funext x; fin_cases x <;> rfl)
  (by intro x y _; fin_cases x <;> fin_cases y <;>
    (first | rfl | simp; trivial))

def p₂ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : p₂ ⊚ a = 𝟙 X := by
  funext x
  cases x <;> rfl

/-!
Exercise III.22 (p. 147)
-/
example : ¬(p₁ ⊚ β = α ⊚ p₁) := by
  intro h
  have h_contra : (p₁ ⊚ β) Y.y₂ = (α ⊚ p₁) Y.y₂ := congrFun h Y.y₂
  dsimp [p₁, α, β] at h_contra
  contradiction

example : ¬(p₂ ⊚ β = α ⊚ p₂) := by
  intro h
  have h_contra : (p₂ ⊚ β) Y.y₂ = (α ⊚ p₂) Y.y₂ := congrFun h Y.y₂
  dsimp [p₂, α, β] at h_contra
  contradiction

/-!
Exercise III.23 (p. 147)
-/
def b₁ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₀

example : b₁ ⊚ β = α ⊚ b₁ := by
  funext y
  cases y <;> rfl

def b₂ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₁

example : b₂ ⊚ β = α ⊚ b₂ := by
  funext y
  cases y <;> rfl

def b₃ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₀

example : b₃ ⊚ β ≠ α ⊚ b₃ := by
  by_contra h
  have h_contra : (b₃ ⊚ β) Y.y₀ = (α ⊚ b₃) Y.y₀ := congrFun h Y.y₀
  dsimp [b₃, α, β] at h_contra
  contradiction

def b₄ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₁

example : b₄ ⊚ β ≠ α ⊚ b₄ := by
  by_contra h
  have h_contra : (b₄ ⊚ β) Y.y₀ = (α ⊚ b₄) Y.y₀ := congrFun h Y.y₀
  dsimp [b₄, α, β] at h_contra
  contradiction

def b₅ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : b₅ ⊚ β ≠ α ⊚ b₅ := by
  by_contra h
  have h_contra : (b₅ ⊚ β) Y.y₂ = (α ⊚ b₅) Y.y₂ := congrFun h Y.y₂
  dsimp [b₅, α, β] at h_contra
  contradiction

def b₆ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : b₆ ⊚ β ≠ α ⊚ b₆ := by
  by_contra h
  have h_contra : (b₆ ⊚ β) Y.y₂ = (α ⊚ b₆) Y.y₂ := congrFun h Y.y₂
  dsimp [b₆, α, β] at h_contra
  contradiction

def b₇ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : b₇ ⊚ β ≠ α ⊚ b₇ := by
  by_contra h
  have h_contra : (b₇ ⊚ β) Y.y₂ = (α ⊚ b₇) Y.y₂ := congrFun h Y.y₂
  dsimp [b₇, α, β] at h_contra
  contradiction

def b₈ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : b₈ ⊚ β ≠ α ⊚ b₈ := by
  by_contra h
  have h_contra : (b₈ ⊚ β) Y.y₂ = (α ⊚ b₈) Y.y₂ := congrFun h Y.y₂
  dsimp [b₈, α, β] at h_contra
  contradiction

/-!
Exercise III.24 (p. 147)
-/
def X' : SimpleGraph := {
  tA := X
  carrierA := Set.univ
  tD := X
  carrierD := Set.univ
  toFun := α
  toFun_mem := fun _ ↦ Set.mem_univ _
}

def Y' : SimpleGraph := {
  tA := Y
  carrierA := Set.univ
  tD := Y
  carrierD := Set.univ
  toFun := β
  toFun_mem := fun _ ↦ Set.mem_univ _
}

def a'' : X' ⟶ Y' := ⟨
  (a, a),
  by
    split_ands
    · exact fun _ _ ↦ Set.mem_univ _
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

example : ¬(∃ p : Y' ⟶ X', p ⊚ a'' = 𝟙 X') := by
  push_neg
  intro p
  obtain ⟨p, _, _, hp_comm⟩ := p
  dsimp [X', Y'] at hp_comm
  have hpβ₀ : ∀ y, (α ⊚ p.1) y = X.x₀ := by
    intro y
    dsimp [α]
    cases p.1 y <;> rfl
  rw [← hp_comm] at hpβ₀
  dsimp [Y'] at hpβ₀
  have hpβ : p.2 (β Y.y₂) = X.x₀ := hpβ₀ Y.y₂
  have hβ : β Y.y₂ = Y.y₁ := rfl
  rw [hβ] at hpβ
  dsimp [CategoryStruct.comp, CategoryStruct.id, a'']
  by_contra h₁
  have h₂ : (p.1 ⊚ a, p.2 ⊚ a) = (𝟙 X, 𝟙 X) :=
    congrArg Subtype.val h₁
  have h₃ : p.2 ⊚ a = 𝟙 X := congrArg Prod.snd h₂
  have hpa₀ : ∀ x, p.2 (a x) = x := congrFun h₃
  have hpa : p.2 (a X.x₁) = X.x₁ := hpa₀ X.x₁
  have ha : a X.x₁ = Y.y₁ := rfl
  rw [ha] at hpa
  rw [hpβ] at hpa
  contradiction

example : ¬(∃ p : Yβ ⟶ Xα, J p ⊚ J a' = J (𝟙 Xα)) := by
  push_neg
  intro p
  obtain ⟨p, _, hp_comm⟩ := p
  dsimp [Xα, Yβ] at hp_comm
  have hpβ₀ : ∀ y, (α ⊚ p) y = X.x₀ := by
    intro y
    dsimp [α]
    cases p y <;> rfl
  rw [← hp_comm] at hpβ₀
  dsimp [Yβ] at hpβ₀
  have hpβ : p (β Y.y₂) = X.x₀ := hpβ₀ Y.y₂
  have hβ : β Y.y₂ = Y.y₁ := rfl
  rw [hβ] at hpβ
  dsimp [CategoryStruct.comp, CategoryStruct.id, a', J,
      functorSetWithEndomapToSimpleGraph]
  by_contra h₁
  have h₂ : (p ⊚ a, p ⊚ a) = (𝟙 X, 𝟙 X) :=
    congrArg Subtype.val h₁
  have h₃ : p ⊚ a = 𝟙 X := congrArg Prod.snd h₂
  have hpa₀ : ∀ x, p (a x) = x := congrFun h₃
  have hpa : p (a X.x₁) = X.x₁ := hpa₀ X.x₁
  have ha : a X.x₁ = Y.y₁ := rfl
  rw [ha] at hpa
  rw [hpβ] at hpa
  contradiction

end ExIII_19_24

/-!
Exercise III.25 (p. 148)
-/
namespace ExIII_25

example {X P Y Q : Type}
    (s t : X ⟶ P) (s' t' : Y ⟶ Q) (fA : X ⟶ Y) (fD : P ⟶ Q)
    (hfSrc_comm : fD ⊚ s = s' ⊚ fA) (hfTgt_comm : fD ⊚ t = t' ⊚ fA)
    : fD ⊚ s = fD ⊚ t ↔ ∀ x, s' (fA x) = t' (fA x) := by
  constructor
  · intro h x
    change (s' ⊚ fA) x = (t' ⊚ fA) x
    rw [← hfSrc_comm, ← hfTgt_comm]
    exact congrFun h x
  · intro h
    rw [hfSrc_comm, hfTgt_comm]
    funext x
    exact h x

variable (XP YQ : IrreflexiveGraph) (f : XP ⟶ YQ)

-- Align to the notation in the book
set_option quotPrecheck false
local notation "fA" => f.val.1
local notation "fD" => f.val.2
set_option quotPrecheck true

local notation "s" => XP.toSrc
local notation "s'" => YQ.toSrc
local notation "t" => XP.toTgt
local notation "t'" => YQ.toTgt

example : (fD ⊚ s = fD ⊚ t) ↔ (∀ x, s' (fA x) = t' (fA x)) := by
  obtain ⟨f, _, _, hfSrc_comm, hfTgt_comm⟩ := f
  dsimp
  constructor
  · intro h x
    change (s' ⊚ f.1) x = (t' ⊚ f.1) x
    rw [← hfSrc_comm, ← hfTgt_comm]
    exact congrFun h x
  · intro h
    rw [hfSrc_comm, hfTgt_comm]
    funext x
    exact h x

end ExIII_25

/-!
Exercise III.26 (p. 148)
-/
namespace ExIII_26

def f : ℤ ⟶ ℚ := fun x ↦ (x : ℚ)

def Z : SetWithEndomap := {
  t := ℤ
  carrier := Set.univ
  toEnd := fun x ↦ 5 * x
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def Q : SetWithEndomap := {
  t := ℚ
  carrier := Set.univ
  toEnd := fun x ↦ 5 * x
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

example : Z ⟶ Q := ⟨
  f,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext (x : ℤ)
      dsimp [Z, Q, f]
      norm_cast
⟩

example : SetWithInvEndomap := {
  t := Q.t
  carrier := Q.carrier
  toEnd := Q.toEnd
  toEnd_mem := fun _ ↦ Set.mem_univ _
  inv := by
    let finv : ℚ ⟶ ℚ := fun x ↦ x / 5
    use finv
    constructor <;> (funext x; dsimp [finv, Q]; ring)
}

example : ∀ {T : Type} (x₁ x₂ : T ⟶ ℤ),
    f ⊚ x₁ = f ⊚ x₂ → x₁ = x₂ := by
  let p : ℚ ⟶ ℤ := fun y ↦ y.num
  have h₁ : p ⊚ f = 𝟙 ℤ := by
    dsimp [f, p]
    funext x
    congr
  intro _ x₁ x₂ h₂
  calc x₁
    _ = 𝟙 ℤ ⊚ x₁ := by rw [Category.comp_id]
    _ = (p ⊚ f) ⊚ x₁ := by rw [h₁]
    _ = p ⊚ f ⊚ x₁ := by rw [Category.assoc]
    _ = p ⊚ f ⊚ x₂ := by rw [h₂]
    _ = (p ⊚ f) ⊚ x₂ := by rw [Category.assoc]
    _ = 𝟙 ℤ ⊚ x₂ := by rw [h₁]
    _ = x₂ := by rw [Category.comp_id]

end ExIII_26

/-!
Exercise III.27 (p. 148)
-/
namespace ExIII_27

inductive X
  | x₀ | x₁

def α : X ⟶ X
    | X.x₀ => X.x₀
    | X.x₁ => X.x₀

def Xα : SetWithIdemEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
  idem := by
    funext x
    cases x <;> rfl
}

example (Yβ : SetWithInvEndomap)
    (f : Xα.toSetWithEndomap ⟶ Yβ.toSetWithEndomap)
    : f X.x₀ = f X.x₁ := by
  obtain ⟨βinv, hβ_inv, _⟩ := Yβ.inv
  obtain ⟨f, _, hf_comm⟩ := f
  have hf_comm_x₀ : (f ⊚ Xα.toEnd) X.x₀ = (Yβ.toEnd ⊚ f) X.x₀ :=
    congrFun hf_comm X.x₀
  have hf_comm_x₁ : (f ⊚ Xα.toEnd) X.x₁ = (Yβ.toEnd ⊚ f) X.x₁ :=
    congrFun hf_comm X.x₁
  dsimp [Xα, α] at hf_comm_x₀ hf_comm_x₁
  have hβfx_eq : Yβ.toEnd (f X.x₀) = Yβ.toEnd (f X.x₁) := by
    rw [← hf_comm_x₀, hf_comm_x₁]
  have h_cancel
      : (βinv ⊚ Yβ.toEnd) (f X.x₀) = (βinv ⊚ Yβ.toEnd) (f X.x₁) :=
    congrArg βinv hβfx_eq
  rwa [hβ_inv] at h_cancel

end ExIII_27

/-!
Exercise III.28 (p. 148)
-/
example (Xα : SetWithEndomap) (Yβ : SetWithInvEndomap)
    (f : Xα ⟶ Yβ.toSetWithEndomap)
    (hf_inj : ∀ {U : Type} (y₁ y₂ : U ⟶ Xα.t),
        f.val ⊚ y₁ = f.val ⊚ y₂ → y₁ = y₂)
    : ∀ {T : Type} (x₁ x₂ : T ⟶ Xα.t),
        Xα.toEnd ⊚ x₁ = Xα.toEnd ⊚ x₂ → x₁ = x₂ := by
  intro _ x₁ x₂ h₁
  have h₂ : f.val ⊚ Xα.toEnd ⊚ x₁ = f.val ⊚ Xα.toEnd ⊚ x₂ := by
    congrm f.val ⊚ ?_
    exact h₁
  repeat rw [Category.assoc, f.property.2] at h₂
  obtain ⟨βinv, hβ_inv⟩ := Yβ.inv
  have h₃ : βinv ⊚ Yβ.toEnd ⊚ f.val ⊚ x₁ =
      βinv ⊚ Yβ.toEnd ⊚ f.val ⊚ x₂ := by
    congrm βinv ⊚ ?_
    exact h₂
  rw [Category.assoc, hβ_inv.1, Category.assoc (f.val ⊚ x₂),
      hβ_inv.1] at h₃
  repeat rw [Category.comp_id] at h₃
  exact hf_inj x₁ x₂ h₃

/-!
Exercise III.29 (p. 150)
-/
/-!
Exercise III.30 (p. 151)
-/
end CM

