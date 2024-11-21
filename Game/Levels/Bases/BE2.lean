import Game.Levels.Bases.BE1

World "Bases"
Level 8
Title "Los elementos de una base de entornos de un punto contienen al punto."

Introduction "Seguimos con propiedades sencillas de las bases de entornos:
cualquier elemento de una base de entornos de un punto, contiene a ese punto."

namespace topo
open topo espacio_topologico Set

variable {X : Type} [espacio_topologico X]

/--
Si `ℬ x` es una base de entornos de un punto, entonces `∀ B ∈ ℬ x, x ∈ B`.
-/
TheoremDoc topo.BE2 as "BE2" in "Bases"

Statement BE2 {ℬ : X → Set (Set X)} (hℬ : ∀ x : X, base_de_entornos x (ℬ x) ) (x : X) :
    ∀ N ∈ ℬ x, x ∈ N := by
  Hint (hidden := true) "Como de costrumnbre, habrá que introducir un
  elemento arbitrario."
  intro N hN
  Hint (hidden := true) "Podemos obtener una propiedad sobre `{x}`
  gracias a `{hℬ}`."
  Hint (hidden := true) "`have h2 := hℬ x`"
  have h2 := hℬ x
  Hint (hidden := true) "Puede ser buen momento para reescribir lo que significa
  ser base de entornos en `{h2}`."
  rw [def_base_de_entornos] at h2
  Hint (hidden := true) "Puedes separar `{h2}` en dos propiedades con `cases'` o `choose`."
  cases' h2 with h3 h4
  Hint (hidden := true) "¿Recuerdas algún teorema previo que se pueda aplicar
  sobre un punto perteneciendo a entornos suyos?"
  Hint (hidden := true) "`apply entornos_N2`"
  apply entornos_N2
  Hint (hidden := true) "Ahora puedes aplicar `{h3}`."
  apply h3
  exact hN

end topo
