import Game.Levels.EspaciosTopologicos.InterseccionFinitaAbiertos

open Set


World "EspaciosTopologicos"
Level 2
Title "El vacio es cerrado."

Introduction "En este nivel y los siguientes
 vamos a tratar con la noción de cerrado en espacios topológicos. Los
 cerrados son los conjuntos cuyo complementario es un abierto.

 Concretamente, vamos a ver que los cerrados cumplen propiedades duales
 de las que definen a los abiertos.

 En este nivel veremos que el vacío es un cerrado. Para ello será útil
 el lema `def_cerrado`, que dice exactamente que un conjunto es cerrado
 si y sólo si su complementario es abierto.
"

open espacio_topologico Set

variable {X : Type} [espacio_topologico X]

def cerrados : (Set (Set X)) := { C | Cᶜ ∈ abiertos}

lemma def_cerrado (C : Set X) : C ∈ cerrados ↔ Cᶜ ∈ abiertos := by rfl

/--
En un espacio topológico, la familia de los cerrados está formada por
los conjuntos cuyo complementario es abierto.

`cerrados = {C | Cᶜ ∈ abiertos}`
-/
DefinitionDoc cerrados as "cerrados"

/--
En un espacio topológico, un conjunto `C` es cerrado, si y sólo si su
complementario es abierto.
-/
TheoremDoc def_cerrado as "def_cerrado" in "Espacios Topológicos"

NewTheorem def_cerrado
NewDefinition cerrados

/--
En un espacio topológico, el vacío es un cerrado.
-/
TheoremDoc cerrado_vacio as "cerrado_vacio" in "Espacios Topológicos"

/--
En un espacio topológico, el vacío es un cerrado.
-/
Statement cerrado_vacio : (∅ : Set X) ∈ cerrados := by
  Hint (hidden := true) "Puedes usar `def_cerrado` para reescribir lo
  que significa que el vacío sea un cerrado."
  rw [def_cerrado]
  Hint (hidden := true) "El complementario del vacío se puede simplificar."
  simp only [compl_empty]
  Hint (hidden := true) "Hay un axioma que te dice exactamente eso."
  exact abierto_total
