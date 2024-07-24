
import Game.Levels.EspaciosMetricos.InterseccionFinitaAbiertoMetrico

variable {X : Type} [espacio_metrico X]
open espacio_metrico

World "EspaciosMetricos"
Level 9

Title "Caracterización de los entornos métricos."

Introduction "Vamos a demostrar una caracterización de los entornos métricos de un punto
que puede ser útil más adelante: un conjunto es entorno métrico de un punto si y sólo si existe un
abierto métrico intermedio.

Este nivel es uno de los más avanzados de este mundo, así que no tendrás tanta ayuda como en los anteriores.
"

/--
Dado un conjunto $E$ de un espacio métrico, y un punto $x$, $E$ es entorno métrico de $x$ si
y solo si existe un abierto métrico $U$ tal que $x \in U \subseteq E$.
-/
TheoremDoc caracterizacion_entorno_metrico as "caracterizacion_entorno_metrico" in "Espacios Métricos"


/--
Un conjunto es entorno métrico de un punto si y sólo si existe un
abierto métrico intermedio.
-/
Statement caracterizacion_entorno_metrico (x : X) (E : Set X) :
    entorno_metrico x E ↔ ∃ (U : Set X), abierto_metrico U ∧ x ∈ U ∧ U ⊆ E := by
  Hint (hidden := true) "Como una doble implicación es en realidad la conjunción de dos implicaciones,
  podemos separar el objetivo en dos con `fconstructor`. "
  fconstructor
  · Hint (hidden := true) "Podemos empezar introduciendo el antecedente del objetivo como hipótesis."
    intro h
    Hint (hidden := true) "Si no sabes qué hacer, prueba a reescribir la definición de entorno métrico."
    Branch
      rw [def_entorno_metrico] at h
      Hint (hidden := true) "Ahora, sabiendo que existe un cierto radio con ciertas propiedades, puedes
      elegir uno."
    choose r hrpos hbE using h
    Hint (hidden := true) "¿Cual puede ser el abierto métrico que puedes usar?"
    Hint (hidden := true) "`use bola {x} {r}`"
    use bola x r
    Hint (hidden := true) "De nuevo hay que separar un objetivo en varias partes."
    fconstructor
    · Hint (hidden := true) "Hay un teorema que se puede aplicar directamente."
      apply bola_abierta
      exact hrpos
    · fconstructor
      · Hint (hidden := true ) "Tal vez convenga reescribir la definición de estar en una bola."
        rw [def_bola]
        Hint (hidden := true) "Hay un resultado que nos dice cuanto es la distancia de un punto a
        sí mismo."
        Branch
          have haux := d1 x
          Hint (hidden := true) "Ahora el objetivo es consecuencia de aritmética lineal."
          linarith
        rw [d1]
        exact hrpos
      · exact hbE
  · Hint (hidden := true) "De nuevo, habrá que introducir el antecedente como hipótesis."
    intro h
    Hint (hidden := true) "Sabiendo que existen abiertos con ciertas propiedades, podemos elegir uno."
    Branch
      cases' h with U hU
      Hint (hidden := true) "Se pueden seguir separando las partes que forman `{hU}` con `cases'`."
    choose U hUab hxU hUE using h
    Hint (hidden := true) "Puedes intentar reescribir qué significa que `{U}` sea abierto métrico."
    Branch
      rw [def_abierto_metrico] at hUab
      Hint (hidden := true) "Si `{U}` es entorno métrico de todos sus puntos, y `{x} ∈ {U}`, en particular
      podemos tener que `{U}` es entorno métrico de `{x}`."
    Branch
      have haux2 := hUab x
      have haux3 := haux2 hxU
    have haux := hUab x hxU
    Hint (hidden := true) "Tal vez puedes reescribir lo que significa ser entorno  métrico."
    Branch
      rw [def_entorno_metrico]
      rw [def_entorno_metrico] at haux
      Hint (hidden := true) "Como sabes que existen números positivos con ciertas propiedades,
      puedes elegir uno de ellos."
      choose r hrpos hrbol using haux
      Hint (hidden := true) "Ahora tienes un radio. ¿Es el que necesitas? Prueba a usarlo."
      use r
      Hint (hidden := true) "Habrá que separar el objetivo en dos."
      fconstructor
      · exact hrpos
      · Hint (hidden := true) "La forma natural de demostrar que un conjunto está contenido en otro,
        es tomar un elemento del primero y ver que debe estar en el segundo."
        intro y hy
        Hint (hidden := true) "Ahora puedes aplicar alguna de las hipótesis."
        apply hUE
        Hint (hidden := true) "Ahora puedes aplicar alguna de las hipótesis."
        apply hrbol
        exact hy
    choose r hrpos hrbol using haux
    Hint (hidden := true) "Ahora tienes un radio. ¿Es el que necesitas? Prueba a usarlo."
    use r
    Hint (hidden := true) "Habrá que separar el objetivo en dos."
    fconstructor
    · exact hrpos
    · Hint (hidden := true) "La forma natural de demostrar que un conjunto está contenido en otro,
      es tomar un elemento del primero y ver que debe estar en el segundo."
      intro y hy
      Hint (hidden := true) "Ahora puedes aplicar alguna de las hipótesis."
      apply hUE
      Hint (hidden := true) "Ahora puedes aplicar alguna de las hipótesis."
      apply hrbol
      exact hy
