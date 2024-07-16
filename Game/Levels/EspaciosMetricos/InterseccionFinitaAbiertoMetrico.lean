
import Game.Levels.EspaciosMetricos.InterseccionAbiertoMetrico

variable {X : Type} [espacio_metrico X]
open espacio_metrico Set Finite

World "EspaciosMetricos"
Level 8

Title "La intersección de una cantidad finita de abiertos métricos es abierto métrico."

Introduction "Hemos visto que la intersección de dos abiertos métricos es abierto métrico. Pero,
¿qué ocurre si en lugar de dos tomas una cantidad mayor? Siempre que la cantidad sea finita, vemos
claro que se puede demostrar igualmente, aplicando repetidamente el argumento anterior.

En este nivel vamos a hacer una demostración algo más compleja que las anteriores, ya que usaremos
*inducción*. Seguramente ya hayas visto demostraciones por inducción con números naturales, pero
hay más situaciones donde se pueden aplicar principios de inducción. Un principio de inducción es un
resultado que afirma que un objeto tiene una cierta propiedad si se cumple para unos casos base,
y que se cumpla para unos casos implica que se cumple para casos derivados de ellos.

Concretamente, aquí vamos a usar un principio de inducción para conjuntos finitos llamado en Lean
`dinduction_on`, y que dice que, si una propiedad es cierta para el conjunto vacío, y si que sea
cierta para un conjunto finito implica que es cierta para el conjunto finito más un nuevo elemento,
entonces es cierta para cualquier conjunto finito.

La forma de hacer demostraciones por inducción en Lean es usando la táctica `induction`. Puedes ver
los detalles sobre cómo usarla en la ayuda.

Además, usaremos dos tácticas nuevas: `left` y `right`, que sirven para demostrar una afirmación que
permite dos opciones, decidiendo cual de las dos queremos demostrar.
"

/--
La táctica `induction` permite aplicar principios de inducción. La forma más sencilla de usarla es
`induction n` donde `n` es un objeto de un tipo que tiene de manera natural un caso base y unos casos
inductivos.

Si el tipo de objeto que quieres usar no tiene de manera natural un principio de inducción asociado
(o quieres usar un principio de inducción más específico), puedes usar `induction s using P`, donde
`P` es el principio de inducción que quieres usar. Si el principio de inducción que quieres usar
precisa de ciertas hipótesis extra, se puede usar con `induction s, h using P`, donde `h` es la
hipótesis adicional.

Por último, si quieres usar cierta hipótesis `g` en el razonamiento de la inducción, puedes usar
`induction s using P generalizing g`.
-/
TacticDoc induction

/--
Si el objetivo es de la forma `P ∨ Q`, `left` pasa a establecer `P` como objetivo.
-/
TacticDoc left

/--
Si el objetivo es de la forma `P ∨ Q`, `wight` pasa a establecer `Q` como objetivo.
-/
TacticDoc right

NewTactic induction left right





lemma interseccion_finita_abierto_metrico (X : Type) [espacio_metrico X] (F : Set (Set X)) (hFfin : Set.Finite F)
    (hFab : ∀ U ∈ F, abierto_metrico U) : abierto_metrico (⋂₀ F) := by
  induction F , hFfin using Finite.dinduction_on
  · simp only [sInter_empty]
    apply total_abierto_metrico
  · simp only [sInter_insert]
    apply interseccion_abiertos_metricos
    · apply hFab
      left
      rfl
    · apply a_2
      intro U hU
      apply hFab
      right
      exact hU
