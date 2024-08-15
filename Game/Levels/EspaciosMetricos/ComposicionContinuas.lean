import Game.Levels.EspaciosMetricos.ContinuidadAbiertos

variable {X Y Z: Type}  [espacio_metrico X] [espacio_metrico Y] [espacio_metrico Z]
open espacio_metrico

World "EspaciosMetricos"
Level 13
Title "Composición de aplicaciones $d$-continuas."

Introduction "En este nivel vamos a usar el resultado anterior para dar
una demostración sencilla de que la composición de aplicaciones $d$-contínuas
es contínua.
"

/--
Dadas dos funciones $d$-contínuas `f: X → Y` y `g : Y → Z`, su composición `g ∘ f` es contínua.

(`∘` se puede teclear con `\comp`)
-/
TheoremDoc composicion_d_continuas as "composicion_d_continuas" in "Espacios Métricos"



/--
Dadas dos funciones $d$-contínuas `f: X → Y` y `g : Y → Z`, su composición `g ∘ f` es contínua.

(`∘` se puede teclear con `\comp`)
-/
Statement composicion_d_continuas (f : X → Y) (g : Y → Z) (hf : d_continua f) (hg : d_continua g) :
    d_continua (g ∘ f) := by
  Hint (hidden := true) "Te recomiendo reescribir el hecho de que las funciones
  sean `d`-continias en términos de abiertos métricos, usando `caracterización_d_continua_abiertos`."
  rw [caracterizacion_d_continua_abiertos] at *
  Hint (hidden := true) "Ahora habrá que tomar un abierto arbitrario de `Z`."
  intro W hW
  Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando `{hg}` a `{W}` y `{hW}`."
  have h2 := hg W hW
  Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis aplicando `{hf}`."
  Hint (hidden := true) "Recuerda que `have` permite usar `_` en lugar de un parámetro si se puede
   deducir de los demás."
  have h3 := hf (g ⁻¹' W) h2
  Hint (hidden := true) "Ya tienes una hipótesis equivalente al objetivo."
  exact h3
