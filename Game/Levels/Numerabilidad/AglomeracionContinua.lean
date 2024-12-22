import Game.Levels.Numerabilidad.LimiteContinua

World "Limites"
Level 7
Title "Límites y continuidad."

Introduction "
En este nivel veremos cómo se comportan los puntos de aglomeración con
las aplicaciones continuas.
"

namespace topo
open topo espacio_topologico Set Function Nat
variable {X Y: Type}  [espacio_topologico X] [espacio_topologico Y]


/--
Si `x` es un punto de aglomeración de una sucesión `s` en un espacio
topológico `X`, y `f : X → Y` es una aplicación continua,
entonces `f x` es punto de aglomeracion de `f ∘ s`.
-/
TheoremDoc topo.aglomeracion_continua as "aglomeracion_continua" in "Limites"

Statement aglomeracion_continua {s : ℕ → X} (f : X → Y) (x : X) (hf : continua f) (hx : aglomeracion s x) : aglomeracion (f ∘ s) (f x) := by
  Hint (hidden := true) "Prueba a reescribir la
  noción de límite en `{hx}` y en el objetivo."
  rw [def_aglomeracion] at hx ⊢
  Hint (hidden := true) "Puedes tomar un abierto arbitrario
  con `intro`."
  intro U hU hfx
  Hint (hidden := true) "Puedes obtener una nueva
  hipótesis (con `have`) si aplicas `{hf}` a `{U}` y `{hU}`."
  have hV := hf U hU
  Hint (hidden := true) "Puedes obtener una nueva hipótesis
  (con `have`) si aplicas `{hx}` a `{f} ⁻¹' {U}`, `{hV}` y `{hfx}`."
  have hx2 := hx (f ⁻¹' U) hV hfx
  Hint (hidden := true) "Toma un número arbitrario con `intro`."
  intro n0
  Hint (hidden := true) "Puedes obtener una nueva hipótesis
  (con `intro`) aplicando `{hx2} a `{n0}`."
  have hx3 := hx2 n0
  Hint (hidden := true) "Gracias a `{hx3}` puedes elegir un número
  natural (con `choose`)."
  choose n hn hnf using hx3
  Hint (hidden := true) "¿Qué número puedes usar?"
  use n
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · exact hn
  · Hint (hidden := true) "Observa que el objetivo es equivalente
    a `{hnf}`."
    exact hnf



end topo
