import Game.Levels.ExteriorFronteraAislado.CaracterizacionExterior
World "ExteriorFronteraAislado"
Level 5
Title "Frontera."

Introduction "La frontera de un conjunto está formada por los puntos
que no son ni interiores ni exteriores.

El teorema `def_frontera` dice exactamente eso. Veamos algunas propiedades
de la frontera.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)

def frontera := {x | x ∉ interior A ∧ x ∉ exterior A}

theorem def_frontera (x : X) : x ∈ frontera A ↔ x ∉ interior A ∧ x ∉ exterior A := by rfl

/--
Dado un conjunto `A` en un espacio topológico,
`def_frontera A` dice que `x ∈ frontera A ↔ x ∉ interior A ∧ x ∉ exterior A`.
-/
TheoremDoc topo.def_frontera as "def_frontera" in "lemas-definición"

/--
La frontera de un conjunto está formada por los puntos que no son ni
interiores ni exteriores.
-/
DefinitionDoc frontera as "frontera"

NewTheorem topo.def_frontera

NewDefinition frontera


/--
Dado un conjunto `A` y un punto `x` en un espacio topológico,
`caracterizacion_frontera A x` dice que `x ∈ frontera A ↔ ∀  U ∈ abiertos, x ∈ U → U ∩ A ≠ ∅ ∧  U ∩ A ≠ U `.
-/
TheoremDoc topo.caracterizacion_frontera as "caracterizacion_frontera" in "Exterior/Frontera/Aislado"


Statement caracterizacion_frontera  (x : X): x ∈ frontera A ↔ ∀  U ∈ abiertos, x ∈ U → U ∩ A ≠ ∅ ∧  U ∩ A ≠ U := by
  Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con  `intro`."
    intro h
    Hint (hidden := true) "Puedes reescribir la definición de estar en la frontera en `{h}`."
    rw [def_frontera] at h
    Hint (hidden := true) "Puedes separar `{h}` en dos hipótesis con `choose` o `cases'`."
    cases' h with h1 h2
    Hint (hidden := true) "Prueba a reescribir la caracterización del interior en `{h1}`."
    rw [caracterizacion_interior] at h1
    Hint (hidden := true) "Prueba a reescribir la caracterización del exterior en `{h2}`."
    rw [def_exterior] at h2
    Hint (hidden := true) "Prueba a reescribir la caracterización del interior en `{h2}`."
    rw [caracterizacion_interior] at h2
    Hint (hidden := true ) "Simplifica (con `simp`) la expresión en `{h1}`."
    simp only [not_exists, not_and] at h1
    Hint (hidden := true ) "Simplifica (con `simp`) la expresión en `{h2}`."
    simp only [not_exists, not_and] at h2
    Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
    intro U hU hxU
    Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Supón que `{U} ∩ {A} = ∅` con `intro`."
      intro hneg
      Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando `{h2}` a `{U}`, `{hU}` y `{hxU}` con `have`."
      have haux := h2 U hU hxU
      Hint (hidden := true) "La contradicción se obtendrá con `{haux}`, así que puedes aplicarla."
      apply haux
      Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
      intro y hyU hyA
      Hint (hidden := true) "Veamos que `{y} ∈ {U} ∩ {A}`. Crea un nuevo objetivo
      para demostrar esto con `have`."
      have hy : y ∈ U ∩ A
      · Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
        fconstructor
        exact hyU
        exact hyA
      Hint (hidden := true) "Puedes usar `{hneg}` para reescribir `{hy}`."
      rw [hneg] at hy
      Hint (hidden := true) "Ahora tienes la contradicción con `{hy}`-"
      apply hy
    · Hint (hidden := true) "Supón que `{U} ∩ {A} = {U}` con  `intro`."
      intro hneg
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
      aplicando `{h1}` a `{U}`, `{hU}` y `{hxU}`-"
      have h3 := h1 U hU hxU
      Hint (hidden := true) "Ahora la contradicción viene de `{h3}`. Puedes aplicarlo."
      apply h3
      · Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
        intro y hy
        Hint (hidden := true) "Puedes usar `{hneg}` para reescribir `{hy}`."
        rw [← hneg] at hy
        Hint (hidden := true) "Puedes separar `{hy}` en dos con `choose` o `cases'`."
        cases' hy with hyU hay
        exact hay
  · intro h
    Hint (hidden := true) "Reescribe el objetico con la definición de frontera."
    rw [def_frontera]
    Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Reescribe con la caracterización de interior"
      rw [caracterizacion_interior]
      Hint (hidden := true) "Supón que existe tal abierto con `intro`."
      intro hneg
      Hint (hidden := true) "Elige un abierto de los que `{hneg}` asegura
      que existen, con `choose`."
      choose U hU hxU hUA using hneg
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
      aplicando `{h}` a `{U}`, `{hU}` y `{hxU}`."
      have h2 := h U hU hxU
      Hint (hidden := true) "Puedes separar `{h2}` en dos con `choose` o `cases'`."
      choose h3 h4 using h2
      Hint (hidden := true) "La contradicción viene de `{h4}`, aplícala."
      apply h4
      Hint (hidden := true) "Prueba a simplificar el objetivo."
      simp only [inter_eq_left]
      exact hUA
    · Hint (hidden := true) "Supón que `{x} ∈ exterior {A}` con `intro`."
      intro hx
      Hint (hidden := true) "Reescribe el objetivo con la caracterización del exterior."
      rw [caracterizacion_exterior] at hx
      Hint (hidden := true) "Elige un abierto de los que `{hx}` asegura
      que existen, con `choose`."
      choose U hU hxU hUA using hx
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
      aplicando `{h}` a `{U}`, `{hU}` y `{hxU}`."
      have h2 := h U hU hxU
      Hint (hidden := true) "Puedes separar `{h2}` en dos con `choose` o `cases'`."
      choose h3 h4 using h2
      Hint (hidden := true) "La contradicción viene con `{h3}`. Prueba a aplicarlo."
      apply h3
      exact hUA



  done
