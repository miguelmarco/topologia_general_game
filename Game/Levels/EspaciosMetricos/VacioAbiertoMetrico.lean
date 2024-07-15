import Game.Levels.EspaciosMetricos.Cerrados

variable {X : Type} [espacio_metrico X]
open espacio_metrico Set

World "EspaciosMetricos"
Level 4

Title "El conjunto vacío es un abierto métrico"

Introduction "En este nivel haremos la primera demostración de que un conjunto es un abierto métrico,
con el conjunto más simple posible: el conjunto vacio.

En este nivel introducimos la táctica `cases'`, que se puede usar para dividir una hipótesis por
casos.
"

/--
Si una hipótesis `h` se puede dar sólo en algunos casos,
la táctica `cases' h`nos separará el objetivo en esos casos.

Se pueden dar nombres concretos a las hipótesis de cada uno de los casos usando `cases' h with h1 h2 ... `.

Por ejemplo, si tenemos una hipótesis `h : P ∨ Q`, `cases' h with h1 h2` nos separará el objetivo en
dos subobjetivos, uno donde tendremos la hipótesis `h1 : P` y otro donde tendremos la hipótesis `h2 : Q`.

Otro uso que se le puede dar a esta táctica es para descomponer una hipótesis formada mediante varias
hipótesis. Por ejemplo, si tenemos una hipótesis `h : P ∧ Q`, `cases' h with h1 h2` nos mantendrá
el objetivo, pero introducirá dos hipótesis  `h1 : P` y `h2 : Q`.
-/
TacticDoc cases'

NewTactic cases'


/--
El conjunto vacio es un abierto métrico.
-/
TheoremDoc vacio_abierto_metrico as "vacio_abierto_metrico" in "Espacios Métricos"

/--
El conjunto vacio es un abierto métrico.
-/
Statement vacio_abierto_metrico  : abierto_metrico (∅  : Set X) := by
  Hint (hidden := true) "Como de costumbre, podemos desarrollar la definición de abierto métrico
  con `rw [def_abierto_metrico]`."
  rw [def_abierto_metrico]
  Hint (hidden := true) "Como el objetivo es una afirmación que se cumple para todo `x` cumpliendo
  `x ∈ ∅`,  podemos introducir el punto con `intro x`."
  intro x
  Hint (hidden := true) "Como el objetivo es una implicación, podemos introducir el antecedente como
  una nueva hipótesis con `intro h`."
  intro h
  Hint "Ahora no está claro qué se puede usar para demostrar el objetivo... pero eso es porque estamos
  suponiendo la hipótesis `{h}`, que no se puede cumplir en ningún caso, porque un elemento nunca puede
  pertenecer al conjunto vacio.

  Así que podemos usar `cases' {h}` para recorrer los posibles casos donde se cumple `{h}`. Como
  no hay ningún caso posible, no habrá nada que demostrar.
  "
  cases' h
