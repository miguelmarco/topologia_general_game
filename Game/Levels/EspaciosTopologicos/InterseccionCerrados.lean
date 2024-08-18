import Game.Levels.EspaciosTopologicos.TotalCerrado
import Mathlib.Data.Set.Lattice

open espacio_topologico Set


World "EspaciosTopologicos"
Level 4
Title "La interseccion de cerrados es cerrado."

Introduction "Vamos a ver un resultado algo más complicado que los anteriores:
la intersección de una familia de cerrados es un cerrado.

Para ello puede ser útil el teorema `compl_sInter`, que permite reescribir
el complementario de la intersección de una familia de conjuntos, como la
unión de los complementarios.
"


TheoremTab "Utilidades"



/--
Si `F` es una familia de conjuntos, `(⋂₀ F)ᶜ = ⋃₀ (compl '' F)`.
-/
TheoremDoc Set.compl_sInter as "compl_sInter" in "Utilidades"

NewTheorem Set.compl_sInter



variable {X : Type} [espacio_topologico X]


/--
Si `F` es una familia cualquiera de cerrados, `⋂₀ F` es un cerrado.
-/
TheoremDoc cerrado_interseccion as "cerrado_interseccion" in "Espacios Topológicos"


/--
Si `F` es una familia cualquiera de cerrados, `⋂₀ F` es un cerrado.
-/
Statement cerrado_interseccion (F : Set (Set X)) (h : F ⊆ cerrados) :
    ⋂₀ F ∈ cerrados := by
  Hint (hidden := true) "Puedes empezar reescribiendo el objetivo mediante
  la definición de cerrado."
  rw [def_cerrado]
  Hint "Puedes usar el teorema `compl_sInter` para reescribir el objetivo."
  rw [compl_sInter]
  Hint (hidden := true) "¿Qué puedes aplicar que demuestre que una unión de
  conjuntos sea un abierto."
  apply union_abiertos
  Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
  lo habitual es tomar un elemento cualquiera del primero y ver que
  debe estar en el segundo."
  intro U hU
  Hint (hidden := true) "`{U}` debe ser el complementario de un conjunto
  de `{F}`. Elige ese conjunto."
  choose C hC hCU using hU
  Hint (hidden := true) "Observa que puedes usar `{hCU}` para reescribir
  el objetivo, pero habrá que usar la igualdad en el sentido contrario."
  rw [← hCU]
  Branch
    rw [← def_cerrado]
    Hint (hidden := true) "La única hipótesis que puedes aplicar para
    demostrar que algo es un cerrado es `{h}`."
    apply h
    Hint (hidden := true) "EL objetivo es exactamente una de las hipótesis."
    exact hC
  Hint (hidden := true) "Ahora tienes dos posibles opciones: o bien
  reescribes el objetivo con `def_cerrado` (pero en sentido contrario),
  o bien demuestras como objetivo secundario que `C ∈ cerrados`."
  have hCC : C ∈ cerrados
  · apply h
    exact hC
  Hint (hidden := true) "Ahora puedes reescribir `{hCC}` con `def_cerrado`."
  rw [def_cerrado] at hCC
  Hint (hidden := true) "El objetivo es exactamente una hipótesis."
  exact hCC
