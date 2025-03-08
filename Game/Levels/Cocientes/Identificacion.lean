import Game.Levels.Cocientes.CocienteT1

World "Cocientes"
Level 9
Title "Identificaciones."

Introduction "
Vamos a introducir la noción de identificación, y su relación con los cocientes.

Una aplicación `f : X → Y` entre espacios topológicos es una **identificación** si
es suprayectiva y la topología en `Y` coincide con la topología final de `f`.

Una consecuencia directa de esta definición es que las identificaciones son
continuas. El teorema `identificacion_continua` dice exactamente eso.

Veamos ahora que la proyección a un cociente es una identificación.
"

namespace topo
open topo espacio_topologico Set Function

variable {X: Type} [espacio_topologico X]

variable {Y : Type} [espacio_topologico Y]


def identificacion (f : X → Y) := Surjective f ∧ ∀ (U : Set Y), U ∈ abiertos ↔ f ⁻¹' U ∈ abiertos

/--
Una aplicación `f : X → Y` entre espacios topológicos se dice que es una
**identificación** si es suprayectiva, y la topología en `Y` es la
topología final de `f`.
-/
DefinitionDoc identificacion as "identificacion"

NewDefinition identificacion

theorem identificacion_continua (f : X → Y) (hf : identificacion f) : continua f := by
  choose hf1 hf2 using hf
  intro U hU
  rw  [hf2] at hU
  exact hU

/--
Si una aplicación `f : X → Y` es una identificación, entonces es continua.
-/
TheoremDoc topo.identificacion_continua as "identificacion_continua" in "Cocientes"

NewTheorem topo.identificacion_continua


/--
Si `R` es una relación de equivalencia en un espacio topológico `X`,
la aplicación `π : X → X /' R` es una identificación.
-/
TheoremDoc topo.cociente_identificacion as "cociente_identificacion" in "Cocientes"

Statement cociente_identificacion [R : Equiv X] : identificacion (π  : X → X /' R) := by
  Hint (hidden := true) "Separa el objetivo en dos partes con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Para ver que es suprayectiva, toma un elemento
    de `{X} /' {R}` (con `intro`), para luego demostrar que tiene preimagen."
    intro x
    Hint (hidden := true) "Observa que el resultado es exactamente lo que dice
    el teorema `existe_representante`, así que puedes aplicarlo."
    apply existe_representante
  · Hint (hidden := true) "Toma un conjunto arbitrario con `intro`."
    intro U
    Hint (hidden := true) "Reescribe lo que significa ser abierto en un cociente."
    rw [def_abierto_cociente]
    Hint (hidden := true) "Observa que ambos lados del objetivo son iguales
    por definición, así que es trivialmente cierto."
    trivial

end topo
