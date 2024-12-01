import Game.Levels.ExteriorFronteraAislado.CaracterizacionExterior
World "ExteriorFronteraAislado"
Level 5
Title "Frontera."

Introduction "La frontera de un conjunto está formada por los puntos
que no son ni interiores ni exteriores.

El teorema `def_frontera` dice exactamente eso. Veamos algunas propiedades
de la frontera.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)

def frontera := {x | x ∉ interior A ∧ x ∉ exterior A}

theorem def_frontera (x : X) : x ∈ frontera A ↔ x ∉ interior A ∧ x ∉ exterior A := by rfl

/--
Dado un conjunto `A` en un espacio topológico,
`def_frontera A` dice que `x ∈ frontera A ↔ x ∉ interior A ∧ x ∉ exterior A`.
-/
TheoremDoc topo.def_frontera as "def_frontera" in "lemas-definición"

/--
La frontera de un conjunto está formada por los puntos que no son ni
interiores ni exteriores.
-/
DefinitionDoc frontera as "frontera"

NewTheorem topo.def_frontera

NewDefinition frontera


/--
Dado un conjunto `A` en un espacio topológico,
`frontera_compl_int_ext as A` dice que `frontera A = (interior A ∪ exterior A)ᶜ`.
-/
TheoremDoc topo.frontera_compl_int_ext as "frontera_compl_int_ext as" in "Exterior/Frontera/Aislado"


Statement frontera_compl_int_ext : frontera A = (interior A ∪ exterior A)ᶜ := by
  Hint (hidden := true) "La forma habitual de demostrar un doble contenido
  es tomar un elemento arbitrario y ver que está en el primer conjunto si
  y solo si está en el segundo. Usa `ext`."
  ext x
  Hint (hidden := true) "Puedes usar la definición de estar en la frontera
  para reescribir el objetivo."
  Hint (hidden := true) "`rw [def_frontera]`"
  rw [def_frontera]
  Hint (hidden := true) "Si te fijas, las expersiones que tienes que ver
  que son equivalentes, esencialmente dicen lo mismo. Sólo hay que
  simplificarlas."
  simp only [compl_union, mem_inter_iff, mem_compl_iff]


end topo
