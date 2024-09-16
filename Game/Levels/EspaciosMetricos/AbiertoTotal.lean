import Game.Levels.EspaciosMetricos.Abiertos

variable {X : Type} [espacio_metrico X]
open espacio_metrico

World "TotalAbiertoMetrico"
Level 3

Title "El espacio total es un abierto métrico"

Introduction "En este nivel veremos que el espacio métrico en sí es un abierto métrico.

El subconjunto formado por todos los puntos del espacio métrico se llama
`univ`.

*Nota*: En la teoría de conjuntos clásica, si `X` es un espacio métrico,
`univ` sería lo mismo que `X`. Sin embargo en la teoría de tipos (que es
la que usa Lean), son objetos de distinto tipo: `X` es un *tipo*, y
la expresión `x : X` significa *x es un objeto de tipo `X`*. Sin embargo
`univ` es un *subconjunto* de `X`, que resulta contener a todos los
objetos de tipo `X`, pero tiene un tipo distinto `univ : Set X`
(es decir `univ` tiene el tipo de los subconjuntos de `X`).

Cuando en una demostración tengamos que dar subconjunto de `X`, podemos
dar `univ`, pero no podemos dar `X`. Puedes pensar en `univ` como
*es el propio `X`, pero pensado como subconjunto de sí mismo*.
"

/--
El conjunto total es un abierto métrico.
-/
Statement abierto_total : abierto_metrico (univ : Set X) := by
  Hint ( hidden := true) "Si no recuerdas la definición de abierto métrico,
  puedes reescribir su definición con `rw [def_abierto_metrico]` o `unfold abierto_metrico`."
  Branch
    rw [def_abierto_metrico]
    Hint (hidden := true) "Ahora puedes tomar un `x` genérico con la táctica `intro`."
  intro x
  Hint (hidden := true) "Se puede usar `intro` para asumir el antecedente como una hipótesis."
  intro h
  Hint (hidden := true) "Si no recuerdas la definición de `entorno_metrico`,
  puedes reescribirla usando `rw [def_entorno_metrico`]."
  Branch
    rw [def_entorno_metrico]
  use 1
  Hint (hidden := true) "Recuerda que puedes separar un objetivo formado por dos partes."
  constructor
  Hint (hidden := true) "Es un resultado de aritmética lineal simple."
  linarith
  intro y
  intro hy
  simp?
