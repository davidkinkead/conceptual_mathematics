import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 9.1 (p. 99)
-/
/-!
Exercise 9.2 (p. 100)
-/
namespace Ex9_2

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}

example : Retract A A := {
  i := 𝟙 A
  r := 𝟙 A
}

example (h₁ : Retract A B) (h₂ : Retract B C) : Retract A C := {
  i := h₂.i ⊚ h₁.i
  r := h₁.r ⊚ h₂.r
}

end Ex9_2

/-!
Splitting
-/
structure Splitting {𝒞 : Type u} [Category.{v, u} 𝒞] {B : 𝒞}
    (e : B ⟶ B) [IsIdempotent e] where
  A : 𝒞
  s : A ⟶ B
  r : B ⟶ A
  rs : r ⊚ s = 𝟙 A
  sr : s ⊚ r = e

/-!
Exercise 9.3 (p. 102)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {B : 𝒞}
    {e : B ⟶ B} [IsIdempotent e]
    (hsr : Splitting e) (hsr' : Splitting e)
    : Iso hsr.A hsr'.A := {
  hom := hsr'.r ⊚ hsr.s
  inv := hsr.r ⊚ hsr'.s
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc hsr'.r, hsr'.sr]
    -- rw [← hsr.sr] needs a bit of hand-holding here
    conv =>
      lhs
      arg 2
      arg 1
      rw [← hsr.sr]
    rw [Category.assoc, hsr.rs]
    rw [← Category.assoc, hsr.rs, Category.id_comp]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc hsr.r, hsr.sr]
    -- rw [← hsr'.sr] likewise needs a bit of hand-holding here
    conv =>
      lhs
      arg 2
      arg 1
      rw [← hsr'.sr]
    rw [Category.assoc, hsr'.rs]
    rw [← Category.assoc, hsr'.rs, Category.id_comp]
}

end CM

