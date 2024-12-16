import Game.Levels.Numerabilidad.Asintotica

World "Numerabilidad"
Level 6
Title "Aglomeración en la clausura."

Introduction "
Veamos que, si una sucesión `s` está contenida en un subconjunto `A`,
un punto de aglomeración de `s` debe estar en la clausura de `A`.
"


namespace topo
open topo espacio_topologico Set Function Nat
variable {X : Type} [espacio_topologico X]


/--
Si una sucesión `s` está contenida en un subconjunto `A`, y `x` es un punto
de aglomeración de `s`, entonces `x` debe estar en la clausura de `A`.
-/
TheoremDoc topo.aglomeracion_clausura as "aglomeracion_clausura" in "Numerabilidad"

Statement aglomeracion_clausura {s : ℕ → X} {A : Set X} {x : X} (hs : ∀ n, s n ∈ A):
    aglomeracion s x → x ∈ clausura A := by
  Hint (hidden := true) "Introduce el antecedente como hipótesis con `intro`."
  intro h
  Hint (hidden := true) "Puede ser útil reescribir la definición de aglomeración."
  rw [def_aglomeracion] at h
  Hint (hidden := true) "Será útil usar la caracterización de puntos en la clausura."
  rw [caracterizacion_clausura]
  Hint (hidden := true) "Puedes tomar un abierto arbitrario (y sus propiedades)
  con `intro`."
  intro U hU hxU
  Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`) aplicando
  `{h}` a `{U}`, `{hU}` y `{hxU}`."
  have h2 := h U hU hxU
  Hint (hidden := true) "En particular, puedes aplicar `{h2}` a cualquier natural
  para obtener una nueva hipótesis (con `have`)."
  have h3 := h2 0
  Hint (hidden := true) "Ahora, como `{h3}` te asegura que existen
  ciertos naturales que cumplen algo, puedes elegir uno con `choose`."
  choose n hn0 hn using h3
  Hint (hidden := true) "Vistas las hipótesis, ¿qué punto puedes usar para
  demostrar que existe alguno como te pide el objetivo?"
  use s n
  Hint (hidden := true) "Habrá que separar el objetivo en dos con `fconstructor`."
  fconstructor
  · exact hn
  · Hint (hidden := true) "Puedes aplicar `{hs}`."
    apply hs

end topo
