import Game.Levels.Interior.AbiertoSiiInterior


World "Interior"
Level 8
Title "Interior del interior."

Introduction "Veamos el operador interior es idempotente: el interior del interior
de un conjunto, es el interior del conjunto.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dado un conjunto `A` en un espacio topológico,
`interior_interior A` dice que `interior (interior A) = interior A`.
-/
TheoremDoc topo.interior_interior as "interior_interior" in "Interior"


Statement interior_interior (A : Set X) : interior (interior A) = interior A:= by
  Hint (hidden := true) "Observa que, gracias a un teorema ya demostrado, el objetivo se
  puede reescribir como que `interior {A}` es abierto."
  rw [← abierto_sii_interior]
  Hint (hidden := true) "Podemos aplicar un teorema que nos asegura que el interior
  de cualquier abierto es abierto."
  apply interior_abierto


end topo
