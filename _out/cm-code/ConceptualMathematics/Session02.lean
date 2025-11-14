import ConceptualMathematics.Article1
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Equality of maps of sets (p. 23)
-/
example {A B : Type} {f g : A ⟶ B}
    : (∀ a : Point A, f ⊚ a = g ⊚ a) → f = g := by
  intro h
  ext a'
  exact congrFun (h (fun _ => a')) ()

end CM

