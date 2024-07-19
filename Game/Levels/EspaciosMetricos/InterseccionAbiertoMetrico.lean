import Game.Levels.EspaciosMetricos.UnionAbiertoMetrico

variable {X : Type} [espacio_metrico X]
open espacio_metrico Set

World "EspaciosMetricos"
Level 7

Title "La intersección de dos abiertos métricos es abierto métrico."

Introduction "¿Qué ocurre si tomas la intersección de dos abiertos métricos? Veamos que resulta ser un
abierto métrico.

Aquí podremos usar la táctica `by_cases`, que nos permite tratar el objetivo por casos: en un caso
asumiendo que una cierta afirmación se cumple, y en el otro asumiendo que no.
"


/--
Dada una proposición `P`, la táctica `by_cases h :P` dividirá el objetivo en dos. En uno de ellos,
estará la hipótesis `h : P` y en el otro, `h : ¬ P`.
-/
TacticDoc by_cases

NewTactic by_cases

/--
La intersección de dos abiertos métricos es un abierto métrico.
-/
TheoremDoc interseccion_abiertos_metricos as "interseccion_abiertos_metricos" in "Espacios Métricos"



/--
La intersección de dos abiertos métricos es un abierto métrico.
-/
Statement interseccion_abiertos_metricos (U V : Set X) (hU : abierto_metrico U) (hV : abierto_metrico V) :
    abierto_metrico (U ∩ V) := by
  Hint (hidden := true) "Puedes empezar reescribiendo la definición de abierto métrico en el
  objetivo y las hipótesis."
  Branch
    rw [def_abierto_metrico]
  Branch
    rw [def_abierto_metrico] at hU
  Branch
    rw [def_abierto_metrico] at hV
  Hint (hidden := true ) "Para demostrar que algo es cierto para todo elemento, puedes hacerlo tomando
  un elemento arbitrario."
  intro x hx
  Hint "`{hx}` nos asegura que `{x} ∈  U ∩ V`, que es lo mismo que `{x} ∈ U` y `{x} ∈ V`."
  Hint (hidden := true) "Puedes separar una hipótesis formada por dos con `cases' {hx} with hxU hxV`."
  cases' hx with hxU hxV
  Hint "Date cuenta de que `{hU}` se puede aplicar a cualquier elemento de `U`."
  Hint (hidden := true) "`have hUentx := {hU} {x} {hxU}` nos dará el resultado de aplicar `{hU}` a `{x}`."
  have hUentx := hU x hxU
  Hint "Y análogamente lo podemos hacer con `V`."
  have hVentx := hV x hxV
  Hint (hidden := true) "Igual es útil reescribir la definición de entorno métrico en donde se pueda."
  Branch
    rw [def_entorno_metrico] at *
  Hint (hidden := true) "Recuerda que, si una hipótesis te asegura la existencia de objetos con
  ciertas propiedades, la táctica `choose` te permite elegir uno."
  choose r1 hr10 hr1 using hUentx
  choose r2 hr20 hr2 using hVentx
  Hint "Ahora date cuenta de que el radio a usar dependerá de cual de si `{r1}` es menor
  que `{r2}`o no."
  Hint (hidden := true) "`by_cases hr : r1 < r2` separará el objetivo en dos, en uno suponiendo que
  `r1 < r2` y en otro suponiendo lo contrario."
  Branch
    by_cases hr : r1 ≤ r2
  by_cases hr : r1 < r2
  · Hint (hidden := true) "Recuerda que para demostrar la existencia de un cierto radio, dando uno
    concreto, se puede usar la táctica `use`."
    use r1
    Hint ( hidden := true) "Se puede separar el objetivo con `fconstructor`."
    fconstructor
    · exact hr10
    · Hint (hidden := true) "Para demostrar que un conjunto está  contenido en otro, toma un elemento
      arbitrario del primero y demuestra que está en el segundo."
      intro y hy
      Hint (hidden := true) "Como `{y} ∈ U  ∩ V` es lo mismo que `{y} ∈ U ∧ {y} ∈ V`, puedes
      separar el objetivo en dos."
      fconstructor
      · apply hr1
        Branch
          rw [def_bola] at *
        exact hy
      · Hint (hidden := true) "Puedes aplicar `{hr2}`."
        apply hr2
        Hint "¿Recuerdas qué significaba que un elemento esté en una bola?"
        Hint (hidden:= true) "Puedes usar `def_bola` para reescribir la pertenencia de `y`
        a las bolas."
        rw [def_bola] at *
        Hint (hidden := true) "Ahora tienes que demostrar una desigualdad, que es consecuencia
        de aplicar aritmética lineal."
        linarith
  · Hint "Este caso es muy parecido al anterior."
    use r2
    fconstructor
    · exact hr20
    · intro y hy
      fconstructor
      · apply hr1
        rw [def_bola] at *
        linarith
      · apply hr2
        exact hy
