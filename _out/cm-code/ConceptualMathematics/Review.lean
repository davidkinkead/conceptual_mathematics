import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import ConceptualMathematics.Session09
import ConceptualMathematics.Summary
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Involution, IsInvolution
-/
structure Involution {𝒞 : Type u} [Category.{v, u} 𝒞] (A : 𝒞) where
  f : A ⟶ A
  invol : f ⊚ f = 𝟙 A

class IsInvolution {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (f : A ⟶ A) where
  invol : f ⊚ f = 𝟙 A

end CM

