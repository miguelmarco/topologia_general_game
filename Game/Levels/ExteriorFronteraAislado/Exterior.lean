import Game.Levels.Interior.UnionInterior
World "ExteriorFronteraAislado"
Level 1
Title "Exterior."

Introduction "El exterior de un conjunto es el interior de su complementario.

El teorema `def_exterior` dice exactamente eso. Veamos algunas propiedades
del exterior.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)

def exterior := interior Aᶜ

theorem def_exterior : exterior A = interior Aᶜ := rfl

/--
Dado un conjunto `A` en un espacio topológico,
`def_exterior A` dice que `exterior A = interior Aᶜ`.
-/
TheoremDoc topo.def_exterior as "def_exterior" in "lemas-definición"

/--
El exterior de un conjunto es el interior de su complementario.
-/
DefinitionDoc exterior as "exterior"

NewTheorem topo.def_exterior

NewDefinition exterior

TheoremTab "Exterior/Frontera/Aislado"

/--
Dado un conjunto `A`  en un espacio topológico,
`exterior_abierto A` dice que `exterior A ∈ abiertos`.
-/
TheoremDoc topo.exterior_abierto as "exterior_abierto" in "Exterior/Frontera/Aislado"


Statement exterior_abierto  : exterior A ∈ abiertos:= by
  Hint (hidden := true) "Reescribe la definición de exterior con `def_exterior`."
  rw [def_exterior]
  Hint (hidden := true) "Puedes aplicar el teorema que dice que el
  interior de cualquier conjunto es abierto."
  apply interior_abierto


end topo
