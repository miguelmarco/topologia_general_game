import Game.Levels.Conexion.ImagenConexo
import Mathlib.Data.Set.Subset

World "Conexión"
Level 5
Title "Clausura de un conexo"

Introduction "En este nivel vamos a ver que la clausura de un subconjunto conexo
es conexa.

Más aún, cualquier conjunto intermedio entre el conexo y su clausura, es conexo.
"

namespace topo
open topo Set espacio_topologico

variable (X : Type) [espacio_topologico X] (A : Set X)



open Set.Notation



/--
Si `X` es un espacio topológico, `A` es un subconjunto conexo, y `B` es
un conjunto entre `A` y su clausura, entonces `B` es conexo.
-/
TheoremDoc topo.clausura_conexo as "clausura_conexo" in "Conexión"

Statement clausura_conexo (hA : conexo A) (B : Set X) (hAB : A ⊆ B) (hB : B ⊆ clausura A) :
    conexo B := by
  Hint (hidden := true) "Puedes reescribir la caracterización de subconjuntos
  conexos en `{hA}` y el objetivo."
  rw [caracterizacion_subespacio_conexo] at hA ⊢
  Hint (hidden := true) "Para ver que no existen abiertos como dice el objetivo,
  supón que existen con `intro`."
  intro hneg
  Hint (hidden := true) "Ahora, para llegar a contradicción, podemos aplicar
  `{hA}` y pasar a demostrar lo que afirma que es falso."
  apply hA
  Hint (hidden := true) "Gracias a `{hneg}`, puedes elegir dos abiertos con ciertas propiedades."
  choose U V h1 h2 h3 h4 h5 h6 using hneg
  Hint (hidden := true) "Para ver que existe un tal abierto, puedes usar `{U}`."
  use U
  Hint (hidden := true) "Puedes usar `{V}`."
  use V
  Hint (hidden := true) "Puedes simplificar las expresiones en `{h3}` `{h4}`
  y el objetivo."
  simp at h3 h4 ⊢
  simp [h1,h2]
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · choose y hyU hyB using h3
    specialize hB hyB
    rw [caracterizacion_clausura] at hB
    specialize hB U h1 hyU
    choose z hz1 hz2 using hB
    use z
  fconstructor
  · choose y hyU hyB using h4
    specialize hB hyB
    rw [caracterizacion_clausura] at hB
    specialize hB V h2 hyU
    choose z hz1 hz2 using hB
    use z
  fconstructor
  · rw [← subset_empty_iff]
    rw [← h5]
    intro x hx
    exact ⟨hx.1,hAB hx.2⟩
  apply subset_trans hAB h6


example {Y : Type} [espacio_topologico Y] (f : X → Y) (hf : continua f) (hX : conexo X) :
    conexo (range f) := by
  rw [caracterizacion_conexo_total] at hX
  rw [← image_univ]
  apply imagen_conexo
  · apply hf
  exact hX


 end topo
