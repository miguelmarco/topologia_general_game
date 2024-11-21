import Game.Levels.Bases.BE4

World "Continuidad"
Level 1
Title "La composición de aplicaciones continuas es continua."

Introduction "Dados dos espacios topológicos `X` e `Y`, una aplicación
`f : X → Y` se dice *continua* si para todo abierto `U` de `Y`,
su preimagen `f ⁻¹' U` es un abierto de de `X` (el símbolo `⁻¹` se obtiene
tecleando `\\-1`).

El lema- definición `def_continua` se puede usar para reescribir
la afirmación de que una función es continua según la definición de
continuidad.

Veamos ahora que la composición de funciones continuas es continua.
"

namespace topo
open topo espacio_topologico Set
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

def continua := ∀ U ∈ abiertos, f⁻¹' U ∈ abiertos

TheoremTab "Continuidad"



/--
Si `f : X → Y` es una aplicación entre espacios topológicos, `def_continua`
dice que `continua f ↔ ∀ U ∈ abiertos, f ⁻¹' U ∈ abiertos`.
-/
TheoremDoc topo.def_continua as "def_continua" in "Lemas-definición"

theorem def_continua : continua f ↔ ∀ U ∈ abiertos, f ⁻¹' U ∈ abiertos := by rfl

NewTheorem topo.def_continua

/--
Si `f : X → Y` y `g : Y → Z` son aplicaciones continuas entre espacios
topológicos, entonces `g ∘ f` es continua.
-/
TheoremDoc topo.composicion_continuas as "composicion_continuas" in "Continuidad"

/--
Si `f : X → Y` y `g : Y → Z` son aplicaciones continuas entre espacios
topológicos, entonces `g ∘ f` es continua.
-/
Statement composicion_continuas {Z : Type} [espacio_topologico Z]
  (g : Y  → Z) (hf : continua f) (hg : continua g) :
      continua (g ∘ f) := by
  Hint (hidden := true) "Podemos reescribir la definición de aplicación
  continua en el objetivo y varias hipótesis."
  rw [def_continua] at hf hg ⊢
  Hint (hidden := true) "Como queremos demostrar algo para todo abierto,
  podemos introducir uno arbitrario y demostrarlo para él."
  intro U hU
  Hint (hidden := true) "Observa que podemos obtener una nueva hipótesis
  si particularizamos `{hg}` para `{U}` y `{hU}`."
  have h2 := hg U hU
  Hint (hidden := true) "Ahora podemos particularizar `{hf}` para
  `g ⁻¹' U` y `{h2}`.

  Como `{h2}` ya no determina el conjunto del que estamos hablando,
  podemos omitirlo escribiendo `_` en su lugar, es decir: `have h3 := `{hf} _ `{h2}`."
  have h3 := hf (g ⁻¹' U) h2
  Hint (hidden := true) "Ahora el objetivo es exactamente una de las hipótesis."
  exact h3

end topo
