import Game.Levels.EspaciosMetricos.TotalAbiertoMetrico

variable {X : Type} [espacio_metrico X]
open espacio_metrico Set

World "EspaciosMetricos"
Level 6

Title "La unión arbitraria de abiertos métricos es abierto métrico."

Introduction "¿Qué ocurre si tomas la unión de abiertos métricos? Veamos que resulta ser un
abierto métrico.

En concreto, vamos a trabajar con la unión de una *familia* de abiertos métricos (es decir, un
conjunto cuyos elementos son conjuntos del espacio métrico).

Aquí introduciremos las tácticas `choose`, `exact` y `apply`.

- `choose` premite elegir un objeto con unas propiedades si tenemos una hipótesis que nos asegura
que existe.

- `exact` nos permite demostrar la existencia de un objeto con una propiedad, dando explícitamente
el objeto en cuestión.

- `apply` permite aplicar un teorema (o hipótesis) que implique el resultado, cambiando el objetivo
a demostrar las hipótesis de ese teorema.

"

/--
Si tienes una hipótesis `h` que asegura la existencia de un objeto `x` con una propiedad `hx`, la táctica
`choose x hx using h` nos permite elegir un tal objeto, y nos da la demostración de que cumple la propiedad.

Si lo que nos asegura la hipótesis es más de una propiedad, se pueden obtener todas ellas; por ejemplo
`choose x hx1 hx2 hx3 using h` nos daría el objeto `x` y las tres afirmaciones `hx1`, `hx2` y `hx3`.

Si la hipótesis `h` nos asegura que para cada elemento de un cierto tipo,
existe un objeto con una cierta propiedad (es decir, es del tipo `∀ x : X, ∃ (O : Y), P O`)
, `choose f hf using h` nos dará una función `f : X → Y` que nos da el objeto
`O` para cada `x`, y una hipótesis
`hf : ∀ x : X, P (f x)` que nos asegura que el correspondiente objeto cumple la propiedad.

Si la hipótesis nos asegura la existencia del objeto sólo para un cierto subconjunto `U`
de `X`,  podemos usar `choose!` en lugar de `choose`, y nos dará igualmente la función `f`,
pero las hipótesis adicionales sólo nos asegurarán las propiedades para las imágenes
de los elementos de `U`.
-/
TacticDoc choose

/--
`exact h` demuestra un objetivo que sea igual que `h`.
-/
TacticDoc exact

/--
Si tienes un resultado `h : P → Q` y tu objetivo es `Q`, `apply h` cambia el objetivo a `P`.
-/
TacticDoc apply

NewTactic choose exact apply
NewHiddenTactic choose! «using»

/--
La unión arbitraria de abiertos métricos es un abierto métrico.
-/
TheoremDoc union_abiertos_metricos as "union_abiertos_metricos" in "Espacios Métricos"

OnlyTactic rw intro choose choose! «have» «using» use fconstructor exact apply trivial

/--
La unión arbitraria de abiertos métricos es un abierto métrico.
-/
Statement union_abiertos_metricos (X : Type) [espacio_metrico X] (F : Set (Set X)) (hF : ∀ U ∈ F, abierto_metrico U) :
    abierto_metrico (⋃₀ F )  := by
  Hint "Aquí, `F` es una *familia* de conjuntos de `X`, que cumple que todos sus miembros son
  abiertos métricos."
  Hint (hidden := true) "Puedes empezar desarrollando la definición de abierto métrico."
  Branch
    rw [def_abierto_metrico]
  Hint (hidden := true) "Como quieres demostrar que algo es cierto para todo `x`, puedes introducir
  un `x` arbitrario con `intro x`."
  intro x
  Hint (hidden := true) "Puedes introducir el antecedente como hipótesis con `intro hx`."
  intro hx
  Hint "Observa que la hipótesis `{hx}` te dice que `{x}` está en la unión de todos los elementos de `F`.
  Es decir, hay algún conjunto `U`, que pertenece a `F`, y al cual pertenece `{x}`."
  Hint (hidden := true) "La táctica `choose U hUF hxU using {hx}` te permitirá elegir un elemento de `F`
  que cumple lo que queremos."
  Branch
    rw [def_entorno_metrico]
  choose U hUF hxU using hx
  Hint "Como todo elemento de `F` es un abierto métrico, y `{U}` es un elemento de `F`... ¿ves cómo
  obtener que `{U}` debe ser abierto métrico?"
  Hint (hidden := true) "`have hUab := hF {U} {hUF}` nos debería dar `hUab : abierto_metrico {U}`."
  have hUab := hF U hUF
  Hint "Como `{U}` es abierto métrico, debe ser entorno de sus puntos, en particular de `{x}`."
  Hint (hidden := true) "`have hUent := {hUab} {x} {hxU}` debería darnos `hUent : entorno_metrico x U`."
  Branch
    rw [def_abierto_metrico] at hUab
  have hUentx := hUab x hxU
  Hint (hidden := true) "Posiblemente sea útil desplegar qué significa ser entorno métrico de `{x}`."
  Hint (hidden := true) "`rw [def_entorno_metrico] at *` aplicará la definición de ser entorno donde se pueda."
  Branch
    rw [def_entorno_metrico] at *
  Hint "Como `{hUentx}` nos dice que existe un número con unas ciertas propiedades, podemos elegirlo."
  Hint (hidden := true) "`choose r hr0 hr using {hUentx}` nos dará un número `r` y sus propiedades
  garantizadas por `{hUentx}`."
  choose r hr0 hr using hUentx
  Hint "¿Qué número positivo podemos usar para garantizar que el objetivo se cumple?"
  Hint (hidden := true) "Para usar `{r}` como número concreo, utiliza `use {r}`."
  use r
  Hint "Como tenemos que demostrar una afirmación construida como conjunción de dos, tendremos
  que separar el objetivo en dos."
  fconstructor
  · Hint (hidden := true) "El objetivo es exactamente igual a una de las hipótesis."
    exact hr0
  · Hint "Para demostrar que un conjunto está contenido en otro, hay que tomar un elemento arbitrario."
    intro y
    Hint "Puedes introducir el antecedente del objetivo como hipótesis."
    intro hy
    Hint "Para demostrar que un elemento está en la unión de una familia, lo más directo es dar un
    elemento de la familia al cual pertenece. ¿Cual puede ser?"
    Hint (hidden := true) "Puedes usar `{U}` como caso concreo con `use {U}`."
    use U
    Hint "De nuevo, el objetivo es una afirmación construida con otras dos."
    fconstructor
    · Hint (hidden := true) "El objetivo es exactamente igual a una de tus hipótesis."
      exact hUF
    · Hint "Observa que tienes que demostrar que un elemento está en `{U}`, pero tienes una hipótesis
      que te dice que otro conjunto está contenido en '{U}`."
      Hint ( hidden := true ) "`apply  {hr}` te permite cambiar el objetivo a que `{y} ∈ bola {x} {r}`."
      apply hr
      Hint "Observa que ahora tu objetivo es exactamente igual a una de tus hipótesis."
      exact hy
