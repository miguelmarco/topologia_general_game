import Game.Levels.ExteriorFronteraAislado.CaracterizacionFrontera
World "ExteriorFronteraAislado"
Level 7
Title "Frontera."

Introduction "La frontera de un conjunto es cerrado.

Para esta demostración, serán útiles un par de lemas sobre conjuntos:

`compl_compl` y `sUnion_pair`.

`compl_compl` dice que el complementario del complementario de un conjunto
es ek propio conjunto.

`sUnion_pair` dice que `⋃₀ {A, B} = A ∩ B`.

Análogamente, `sInter_pair` dice que `⋂₀ {A , B} = A ∩ B`.
"



namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Dado un conjunto `A`, `compl_compl A` dice que `Aᶜᶜ = A`
-/
TheoremDoc compl_compl as "compl_compl" in "Utilidades"

/--
Dados conjuntos `A` y `B`, `sUnion_pair A B` dice que `⋃₀ {A, B} = A ∪ B`
-/
TheoremDoc Set.sUnion_pair as "sUnion_pair" in "Utilidades"


/--
Dados conjuntos `A` y `B`, `sInter_pair A B` dice que ` ⋂₀ {A, B} = A ∩ B`
-/
TheoremDoc Set.sInter_pair as "sInter_pair" in "Utilidades"

NewTheorem compl_compl Set.sUnion_pair Set.sInter_pair

/--
Dado un conjunto `A`  en un espacio topológico,
`frontera_cerrado A` dice que `frontera A ∈ cerrados`.
-/
TheoremDoc topo.frontera_cerrado as "frontera_cerrado" in "Exterior/Frontera/Aislado"


Statement frontera_cerrado : frontera A ∈ cerrados := by
  Hint (hidden := true) "Prueba a reescribir la frontera
  como complementario de la unión y el exterior."
  rw [frontera_compl_int_ext]
  Hint (hidden := true) "Ahora prueba a reescribir la definición
  de cerrado."
  rw [def_cerrado]
  Hint (hidden := true) "Puedes usar `compl_compl` para reescribir el objetivo."
  rw [compl_compl]
  Hint (hidden := true) "Ahora Nos convendría reescribir la unión de dos
  conjuntos como la unión de una familia (para poder aplicar que la
  unión de familias de abiertos son abiertos). Para ello, puedes
  usar `sUnion_pair`."
  rw [← sUnion_pair]
  Hint (hidden := true) "Ahora ya podemos aplicar que la unión de cualquier
  familia de abiertos es un abierto."
  apply union_abiertos
  Hint (hidden := true) "Como tenemos que ver que una familia está
  contenida en otra, puedes tomar un elemento arbitrario de la primera
  con `intro`."
  intro U hU
  Hint (hidden := true) "Prueba a simplificar `{hU}`."
  simp at hU
  Hint (hidden := true) "Ahora `{hU}` nos asegura que estamos en dos
  casos posibles. Trata cada uno como un objetivo separado con `cases'`."
  cases' hU with hU hU
  Hint (hidden := true) "Gracias a `{hU}`, podemos reescribir el objetivo."
  rw [hU]
  Hint (hidden := true) "Podemos aplicar un teorema que asegura que el interior
  de un conjunto es abierto."
  apply interior_abierto
  Hint (hidden := true) "Gracias a `{hU}`, podemos reescribir el objetivo."
  rw [hU]
  Hint (hidden := true) "Puedes aplicar un teorema que asegura que el exterior
  de un conjunto es abierto."
  apply exterior_abierto


end topo
