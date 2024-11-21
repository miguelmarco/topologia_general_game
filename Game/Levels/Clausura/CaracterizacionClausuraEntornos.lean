import Game.Levels.Clausura.CaracterizacionClausura


World "Clausura"
Level 2
Title "Caracterización de clausura por entornos"

Introduction "Veamos una caracterización similar a la anterior, pero
usando entornos.

Esta demostración será fácil gracias a la anterior.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]


/--
Un punto `x` está en la clausura de `A` si y sólo si todo
entorno de `x`, interseca a `A`.
-/
TheoremDoc topo.caracterizacion_clausura_entornos as "caracterizacion_clausura_entornos" in "Clausura"

Statement caracterizacion_clausura_entornos (A : Set X) (x : X) : x ∈ clausura A ↔ ∀ N, entorno x N → ∃ y, y ∈ N ∩ A := by
  Hint (hidden := true) "Será todo más fácil si usas la caracterización
  anterior para reescribir el objetivo."
  rw [caracterizacion_clausura]
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h N hN
    Hint (hidden := true) "`{hN}` te asegura que existen abiertos intermedios,
    elige uno con `choose`."
    choose U hUab hxU hUN using hN
    Hint (hidden := true) "Observa que puedes obtener una nueva hipótesis
    si particularizas `{h}` a `{U}`, `{hUab}` y `{hxU}`."
    have h2 := h U hUab hxU
    Hint (hidden := true) "`{h2}` ahora te asegura que existen ciertos `y`s, elige
    uno con `choose`."
    choose y hyU hyA using h2
    Hint (hidden := true) "Ahora puedes usar `{y}` para demostrar que existe uno como quieres."
    use y
    fconstructor
    · apply hUN
      exact hyU
    · exact hyA
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h U hU hxU
    Hint (hidden := true) "Puedes aplicar directamente `{h}`."
    apply h
    · Hint (hidden := true) "Te será útil reescribir `{hU}` en términos
      de ser entorno de sus puntos."
      rw [abierto_sii_entorno] at hU
      apply hU
      exact hxU

end topo
