import Game.Levels.Numerabilidad.LimiteClausura

World "Limites"
Level 6
Title "Límites y continuidad."

Introduction "
En este nivel veremos cómo se comportan los límites con
las aplicaciones continuas.
"

namespace topo
open topo espacio_topologico Set Function Nat
variable {X Y: Type}  [espacio_topologico X] [espacio_topologico Y]


/--
Si `x` es un límite de una sucesión `s` en un espacio
topológico `X`, y `f : X → Y` es una aplicación continua,
entonces `f x` es límite de `f ∘ s`.
-/
TheoremDoc topo.limite_continua as "limite_continua" in "Limites"

Statement limite_continua {s : ℕ → X} (f : X → Y) (x : X) (hf : continua f) (hx : limite s x) : limite (f ∘ s) (f x) := by
  Hint (hidden := true) "Prueba a reescribir la
  noción de límite en `{hx}` y en el objetivo."
  rw [def_limite] at hx ⊢
  Hint (hidden := true) "Puedes tomar un abierto arbitrario
  con `intro`."
  intro U hU hfx
  Hint (hidden := true) "Puedes obtener una nueva
  hipótesis (con `have`) si aplicas `{hf}` a `{U}` y `{hU}`."
  have hV := hf U hU
  Hint (hidden := true) "Puedes obtener una nueva hipótesis
  (con `have`) si aplicas `{hx}` a `{f} ⁻¹' {U}`, `{hV}` y `{hfx}`."
  have hx2 := hx (f ⁻¹' U) hV hfx
  Hint (hidden := true) "Gracias a `{hx2}`, puedes elegir un natural `n0`."
  choose n0 hn0 using hx2
  Hint (hidden := true) "¿Qué número natural puedes usar?"
  use n0
  Hint (hidden := true) "Toma un número arbitrario con `intro`."
  intro n hn
  Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
  aplicando `{hn0}` a `{n}` y `{hn}`."
  have hn1 := hn0 n hn
  Hint (hidden := true) "Puedes simplificar las expresiones en `{hn1}`
  y el objetivo."
  simp only [mem_preimage, comp_apply] at hn1 ⊢
  exact hn1


end topo
