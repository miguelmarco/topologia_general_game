import Game.Levels.Bases.BE3



World "Bases"
Level 10
Title "Otra propiedad de las bases de entornos."

Introduction "Veamos la última propiedad fundamental de las bases de entornos.
Esta propiedad tiene que ver con la existencia de un conjunto intermedio
en cada abierto básico, de manera que hay un abierto básico intermedio
para cada punto de ese conjunto."

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]


/--
Si para cada punto `z` de un espacio `ℬ z` es una base de entornos de
`z`, y `x` es un punto, entonces `∀ Bx ∈ ℬ x , ∃ W ∈ ℬ x, ∀ y ∈ W, ∃ By ∈ ℬ y, By ⊆ Bx `.
-/
TheoremDoc topo.BE4 as "BE4" in "Bases"

Statement BE4 {ℬ : X → Set (Set X)} (hℬ : ∀ x : X, base_de_entornos x (ℬ x) ) (x : X) :
    ∀ Bx ∈ ℬ x , ∃ W ∈ ℬ x, ∀ y ∈ W, ∃ By ∈ ℬ y, By ⊆ Bx := by
  Hint (hidden := true) "Como de costumbre, ya que hay que demostrar algo para todo
  conjunto de una familia, habrá que introducir uno arbitrario."
  intro Bx hBx
  Hint (hidden := true) "Podemos obtener una nueva hipótesis particularizando
   {hℬ} para `{x}`."
  Hint (hidden := true) "`have h2 := {hℬ} {x}`"
  have h2 := hℬ x
  Hint (hidden := true) "Puede ser buen momento para reescribir la definición
  de base de entornos en `{h2}`."
  rw [def_base_de_entornos] at h2
  Hint (hidden := true) "Puedes separar `{h2}` en dos hipótesis usando
  `choose` o `cases'`."
  choose h2 h3 using h2
  Hint (hidden := true) "Puedes obtener una nueva hipótesis particularizando
  `{h2}` para `{Bx}` y `{hBx}`."
  have h4 := h2 Bx hBx
  Hint (hidden := true) "Prueba a reescribir la definición de entorno en
   `{h4}`."
  rw [def_entorno] at h4
  Hint (hidden := true) "Como `{h4}` te asegura que existen abiertos con unas ciertas
  propiedades, puedes elegir uno con `choose`."
  choose U hUab hxU hUBx using h4
  Hint (hidden := true) "Para poder progresar con {h3}, necesitas ver que `{U}` es
  entorno de `{x}`. Para ello debes enunciar esa afirmación, y te aparecerá
  un nuevo objetivo para demostrarla. Recuerda que la táctica para ello es `have`."
  Hint (hidden := true) "`have hUen : entorno {x} {U}`"
  have hUen : entorno x U
  · Hint (hidden := true) "Prueba a reescribir la definición de entorno."
    rw [def_entorno]
    Hint (hidden := true) "Ahora solo tienes que saber qué abierto usar."
    Hint (hidden := true) "`use {U}`"
    use U
  Hint (hidden := true) "Ahora ya puedes obtener una nueva hipótesis particularizando
  `{h3}` para `{U}` y `hUen`."
  have h5 := h3 U hUen
  Hint (hidden := true) "Ahora `{h5}` te asegura que existen elementos de
  `{ℬ} {x}` contenidos en `{U}`. Puedes elegir uno (y sus propiedades)
  con `choose`."
  choose W hW hWU using h5
  Hint (hidden := true) "Ahora ya tienes el elemento de `{ℬ} {x}` que puedes
  usar."
  Hint (hidden := true) "`use {W}`"
  use W
  Hint (hidden := true) "Tendrás que separar el objetivo en varios con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Este objetivo es exactamente una de tus hipótesis."
    exact hW
  · Hint (hidden := true) "Ahora tienes que demostrar algo para todo punto de `{W}`,
    así que tendrás que introducir uno arbitrario."
    intro y hy
    Hint (hidden := true) "Observa que puedes obtener una nueva hipótesis
    si particularizas `{hℬ}` a `{y}`."
    Hint (hidden := true) "`have hyB := {hℬ} {y}`"
    have hyB := hℬ y
    Hint (hidden := true) "¿Recuerdas qué quería decir ser base de entornos?
    Si lo tienes claro, puedes separar `{hyB}` directamente en sus partes usando
    `choose`. Si no lo ves del todo claro, puedes reescribir la definición
    en `{hyB}`."
    rw [def_base_de_entornos] at hyB
    Hint (hidden := true) "Ahora ya puedes separar `{hyB}` en sus partes
    con `choose` o `cases'`."
    choose hyB1 hyB2 using hyB
    Hint (hidden := true) "Observa que `{hyB2}` implicaría lo que queremos,
    si pudieramos demostrar sus condiciones. Así que lo podemos aplicar."
    Hint (hidden := true) "`apply `{hyB2}`."
    apply hyB2
    Hint (hidden := true) "¿Recuerdas la definición de entorno? Si la tienes
    clara, puedes seguir directamente como si el objetivo estuviera escrito
    como su definición desarrollada.

    Si no lo tienes claro, reescribe la definición."
    rw [def_entorno]
    Hint (hidden := true) "Hay que dar un abierto que cumpla ciertas propiedades,
    ¿ves cual puedes usar?"
    use U
    Hint (hidden := true) "Ahora hay que separar el objetivo en varios con
    `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Este subobjetivo es exactamente una de tus hipótesis."
      exact hUab
    Hint (hidden := true) "Volvemos a tener que separar el objetivo en varios."
    fconstructor
    · Hint (hidden := true) "Observa que puedes aplicar `{hWU}`"
      apply hWU
      exact hy
    · exact hUBx

end topo
