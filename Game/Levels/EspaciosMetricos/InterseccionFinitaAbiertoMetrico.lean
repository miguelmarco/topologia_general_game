
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
`Set.Finite.dinduction_on`, y que dice que, si una propiedad es cierta para el conjunto vacío, y si que sea
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

/--
`rfl` permite demostrar que un objeto es igual a sí mismo.
-/
TacticDoc rfl

NewTactic induction left right rfl

TheoremTab "Inducción"

/--
`Set.Finite.dinduction_on` es un principio de inducción que asegura que permite demostrar que los
conjuntos finitos cumplen una cierta propiedad, demostrando que la cumple el conjunto vacio, y que
si la cumple un conjunto finito, al añadirle un elemento también la cumple.

Concretamente, si tenemos un conjunto `S`, y una hipótesis `hS : Finite S`, y el objetivo es
demostrar `P S` donde `P` es una cierta propiedad, la táctica
`induction S, hS using Set.Finite.dinduction_on` establecerá dos objetivos: en uno habrá que
demostrar `P ∅`, y en el otro tendremos que demostrar `P (insert a s)` donde `s` es un conjunto
finito, `a` un elemento que no está en `s`, y se tiene la hipótesis de inducción `h : P s`.
-/
TheoremDoc Set.Finite.dinduction_on as "Set.Finite.dindution_on" in "Inducción"

NewTheorem Set.Finite.dinduction_on

/--
La intersección de una familia finita de abiertos métricos es abierto métrico.
-/
TheoremDoc interseccion_finita_abierto_metrico as "interseccion_finita_abierto_metrico" in "Espacios Métricos"

/--
La intersección de una cantidad finita de abiertos métricos es abierto métrico.
-/
Statement interseccion_finita_abierto_metrico (F : Set (Set X)) (hFfin : Set.Finite F)
    (hFab : ∀ U ∈ F, abierto_metrico U) : abierto_metrico (⋂₀ F) := by
  Hint "Esta demostración se presta a usar un principio de inducción."
  Hint ( hidden := true ) "Usa `induction F , hFfin using Finite.dinduction_on`."
  induction F , hFfin using Finite.dinduction_on
  · Hint "Observa que, como caso base, tenemos que demostrar la propiedad para la familia vacía.

    Se puede simplificar la interesección de la familia vacía."
    Hint( hidden := true) "Recuerda que la táctica `simp` puede usarse para simplificar expresiones."
    simp only [sInter_empty]
    Hint (hidden := true) "Ahora hay que demostrar que el conjunto total es abierto. Tenemos un teorema específicamente
    para eso."
    exact total_abierto_metrico
  · Hint "Ahora tenemos que demostrar el paso de inducción. Tenemos un conjunto finito `{s}` que
    cumple la propiedad, y debemos demostrar que al añadirle un elemento `a` también la cumple.

    De nuevo, podemos simplificar la intersección de una familia a la que se le añade un conjunto."
    Hint (hidden := true) "Recuerda que se pueden simplificar expresiones con `simp`."
    simp only [sInter_insert]
    Hint "Ahora lo que tenemos es la intersección de exactamente dos conjuntos, se puede aplicar un
    teorema específico para este caso."
    Hint (hidden := true) "`apply interseccion_abiertos_metricos` nos permitirá demostrar el objetivo
    (si podemos demostrar que tanto `{a}` como `⋂₀ {s}` son abiertos métricos)."
    apply interseccion_abiertos_metricos
    · Hint "Hay una hipótesis que implica el objetivo. Mira a ver cómo aplicarla."
      Hint (hidden := true) "`apply {hFab}` debería permitirnos progresar."
      apply hFab
      Hint "Que un elemento esté en `insert {a} {s}` quiere decir que, o bien es `{a}`, o bien está en `{s}`."
      Hint (hidden := true) "Estamos en una situación en la que hay que demostrar que se da uno
      de entre dos casos posibles. ¿Cual se da concretamente? ¿El primero o el segundo?"
      Hint (hidden := true) "`left` nos dirá que demostremos que `{a}` es `{a}`."
      left
      Hint "Esto es cierto por definición."
      Hint (hidden := true) "La táctica `rfl` demuestra exactamente estos casos."
      rfl
    · Hint "Ahora hay que demostrar que la otra parte también es abierto métrico. Tenemos una hipótesis
      que implica el objetivo."
      Hint (hidden := true) "`apply {a_2}` nos permite aplicar una hipótesis que implica el objetivo."
      apply a_2
      Hint "Hay que demostrar que los conjuntos de la familia `{s}` son abiertos métricos."
      Hint (hidden := true) "Habrá que tomar un conjunto genérico de `{s}` con `intro`."
      intro U
      Hint (hidden := true) "Otra vez `intro` para introducir el antecedente como hipótesis."
      intro hU
      Hint (hidden := true) "Se puede aplicar `{hFab}`."
      apply hFab
      Hint (hidden := true) "`{U} ∈ insert {a} {s}` se puede simplificar como `{U} = {a} ∨ {U} ∈ {s}`."
      Branch
        simp only [mem_insert_iff]
        Hint "¿Cual de los dos casos es el que se da?"
        Hint (hidden := true) "¿El izquierdo o el derecho?"
      right
      Hint (hidden := true) "Ahora el objetivo es exactamente lo que afirma la hipótesis `{hU}`."
      exact hU
