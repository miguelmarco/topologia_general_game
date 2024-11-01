import Game.Levels.Bases.BaseEntornosSii

open espacio_topologico Set


World "Bases"
Level 7
Title "Todo punto tiene una base de entronos no vacía."

Introduction "Vamos a ver algunas propiedades básicas de las bases de entornos.
La primera es muy sencilla: cualquier base de entornos de un punto es no vacía."

variable {X : Type} [espacio_topologico X]


/--
Si para cada punto `x` tenemos una base de entornos `ℬ x`, entonces
hay algún elemento en cada `ℬ x`.
-/
TheoremDoc BE1 as "BE1" in "Bases"

/--
Si para cada punto `x` tenemos una base de entornos `ℬ x`, entonces
hay algún elemento en cada `ℬ x`.
-/
Statement BE1 {ℬ : X → Set (Set X)} (hℬ : ∀ (x : X), base_de_entornos x (ℬ x)) :
    ∀ x : X, ∃ (B : Set X), B ∈ (ℬ x) := by
  Hint (hidden := true) "Como de costumbre, habrá que introducir un `x` arbitrario
  y demostrar la propiedad para él."
  intro x
  Hint (hidden := true) "Observa que podemos obtener una afirmación sobre `{x}` si
  le aplicas `{hℬ}`. Recuerda que se puede obtener `ℬ` tecleando `\\McB`."
  Hint (hidden := true) "`have hx := {hℬ} {x}`"
  have hx := hℬ x
  Hint (hidden := true) "Tal vez sea buen momento para reescribir lo que
  significa que `{ℬ} {x}` sea una base de entornos de `{x}`."
  rw [def_base_de_entornos] at hx
  Hint (hidden := true) "Puedes separar `{hx}` en dos hipótesis con `cases'` o `choose`."
  cases' hx with hx1 hx2
  Hint (hidden := true) "Para poder usar `{hx2}` necesitas un entorno de `{x}`.
  ¿Recuerdas algún teorema que te asegure que existe?."
  Hint (hidden := true) "`have h4 := entornos_N1 {x}`"
  have h4 := entornos_N1 x
  Hint (hidden := true) "Ahora, como sabemos que existen entornos de `{x}`, podemos
  elegir uno con `choose`."
  choose N hN using h4
  Hint (hidden := true) "Ahora ya puedes obtener una nueva hipótesis con
  {hx2} aplicado a `{N}` y `{hN}`."
  Hint (hidden := true) "`have h5 := {hx2} {N} {hN}`"
  have h5 := hx2 N hN
  Hint (hidden := true) "Como sabes que existen elementos de `{ℬ} {x}`,
  puedes elegir uno (y sus propiedades) con `choose`."
  choose B hB hB2 using h5
  use B
