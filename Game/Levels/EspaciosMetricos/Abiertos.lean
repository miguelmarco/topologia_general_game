import Game.Levels.EspaciosMetricos.Distancias

variable {X : Type} [espacio_metrico X]
open espacio_metrico

World "EspaciosMetricos"
Level 2

Title "Abiertos"

Introduction "En este nivel veremos la definición entorno, bola y abierto; y demostraremos
una relación entre estos conceptos.

Dado un punto $x$ en un espacio métrico $X$, y un número real positivo $r$, la *bola*
de centro $x$ y radio $r$ es el conjunto de puntos del espacio que están a distancia de $x$
menor que $r$. Es decir:

$$
\\mathbb{B}(x,r) := \\{y \\in X \\mid d(x,y) < r\\}
$$

Un conjunto $E$ es un *entorno métrico* de $x$ si hay una bola centrada en $x$, que está contenida en $E$.

Un conjunto se dice *abierto métrico* si es entorno métrico de todos sus puntos.

Podemos usar los siguientes resultados-definición:

Si `x` e `y` son puntos de un espacio métrico, y `r` es un número real positivo, `def_bola x y r`
dice que `y ∈ bola x r ↔ d x y < r`.

Si `x` es un punto, y `E` es un conjunto,
`def_entorno_metrico x E` dice que `entorno_metrico x E ↔ ∃ r > 0, bola x r ⊆ E`.

Si `U` es un conjunto, `def_abierto_metrico  U` dice que `abierto_metrico U ↔ ∀ x ∈ U, entorno x U`.

Estos lemas se pueden usar con la táctica `rw`, que permite reescribir una parte del objetivo
(o de una hipótesis) por otra equivalente.

Si la expresión `t` es una prueba de una afirmación de la forma `P ↔ Q`, entonces la táctica
`rw [t]` reemplazará `P` en cualquier lugar donde aparezca en la meta con `Q`. Si deseas
reemplazar `Q` con `P`, usa `rw [← t]`. (Escribe `\\l` para ingresar el símbolo `←`.) Para
realizar el reemplazo en una suposición `h`, usa `rw [t] at h`.

La táctica `rw` también se puede usar con ecuaciones. Si `t` es una prueba de una ecuación
`p = q`, entonces `rw [t]` reemplazará `p` con `q` dondequiera que aparezca, y `rw [← t]`
reemplazará `q` con `p`.

Para realizar múltiples reemplazos, uno después de otro, coloca una lista de pruebas dentro de los corchetes, así:
`rw [t1, t2]`.
"

def bola (x : X) (r : ℝ ) := { y | d x y < r}

/--
Dado un punto $x$ en un espacio métrico $X$, y un número real positivo $r$, la *bola*
de centro $x$ y rdio $r$ es el conjunto de puntos del espacio que están a distancia de $x$
menor que $r$. Es decir:

$$
\mathbb{B}(x,r) := \{y \in X \mid d(x,y) < r\}
$$
-/
DefinitionDoc bola as "bola"


TheoremTab "lemas-definición"

lemma def_bola (x y : X) (r : ℝ ) : y ∈ bola x r ↔ d x y < r := by rfl

/--
`bola_def x y r ` es la prueba de que $y ∈ \\mathbb{B}(x,r) \\iff d(x,y) < r$
-/
TheoremDoc def_bola as "def_bola" in "lemas-definición"


def entorno_metrico (x : X) (E : Set X) := ∃ r > 0, bola x r ⊆ E

/--
Un conjunto $E$ es un *entorno métrico* de $x$ si hay una bola centrada en $x$, que está contenida en $E$.
-/
DefinitionDoc entorno_metrico as "entorno_metrico"


lemma def_entorno_metrico  (x : X) (E : Set X) : entorno_metrico x E ↔ ∃ r > 0, bola x r ⊆ E := by rfl

/--
`def_entorno_metrico x E` es la prueba de que `entorno_metrico x E ↔ ∃ r > 0, bola x r ⊆ E`
-/
TheoremDoc def_entorno_metrico as "def_entorno_metrico" in "lemas-definición"


def abierto_metrico (U : Set X) := ∀ x ∈ U, entorno_metrico x U

/--Un conjunto $U$ es *abierto métrico* si es entorno métrico de todos sus puntos-/
DefinitionDoc abierto_metrico as "abierto_metrico"

NewDefinition bola entorno_metrico abierto_metrico

lemma def_abierto_metrico (U : Set X) : abierto_metrico U ↔ ∀ x ∈ U, entorno_metrico x U  := by rfl

/--
`def_abierto U` es la prueba de que `abierto U ↔ ∀ x ∈ U, entorno x U`.
-/
TheoremDoc def_abierto_metrico as "def_abierto_metrico" in "lemas-definición"




/--
Si el objetivo es de la forma `∃ (x : X), P x`, donde `P` es una cierta propiedad
que pueden cumplir los términos del tipo `X`; e `y` es un término concreto
de tipo `X`, la táctica `use y` cambiará el objetivo a demostrar `P y`.
-/
TacticDoc use

/--
Si el objetivo está formado por la conjunción
de varias partes  (por ejemplo, si es de la forma `P ∧ Q`), la táctica
`constructor` lo separará en dos objetivos distintos: un primer objetivo
en el que hay que demostrar `P` y otro en el que hay que demostrar `Q`.
-/
TacticDoc constructor

/--
Si el objetivo es de la forma `P → Q`, la táctica `intro h` introducirá
una hipótesis de tipo `h : P`, y cambiará el objetivo a `Q`.

Si el objetivo es de la forma `∀ x, P x`, la táctica `intro x` introducirá
un nuevo objeto arbitrario `x`, y cambiará el objetivo a demostrar `P x`.
-/
TacticDoc intro

NewTactic use constructor intro

/--
Las bolas son conjuntos abiertos
-/
TheoremDoc bola_abierta as "bola_abierta" in "Espacios Métricos"

NewTheorem def_bola def_entorno_metrico def_abierto_metrico



/--Las bolas son conjuntos abiertos-/
Statement bola_abierta (c : X) (r : ℝ ) (hr : r > 0) : abierto_metrico (bola c r) := by
  Hint "Podemos empezar reescribiendo la definición de ser un conjunto abierto."
  Hint (hidden := true) "`rw [deb_abierto]` cambiará la afirmación de que la bola es un conjunto
   abierto por su definición"
  rw [def_abierto_metrico]
  Hint "Como hay que demostrar que algo se cumple para todo `x`, habrá que tomar un `x` y demostrarlo
    para él."
  Hint (hidden := true) "Tecleando `intro x` tomaremos un `x` cualquiera."
  intro x
  Hint "Ahora hay que demostrar una implicación, así que habrá que asumir la hipótesis"
  Hint (hidden := true) "`intro h` asumirá la hipótesis"
  intro h
  Hint "Sería útil desarrollar la noción de entorno"
  Hint (hidden := true) "`rw [def_entorno]` aplicará el resultado que afirma
  la definición de entorno."
  rw [def_entorno_metrico]
  Hint  (hidden := true) "`rw [def_bola] at h` aplicará el resultado que
  afirma la definición de bola en la hipótesis `h`."

  rw [def_bola] at h
  Hint "Ahora tienes que demostrar que existe un número real que cumple una cierta
  propiedad. ¿Sabes cual puede ser?.

  Una vez  lo tengas claro, utiliza la táctica `use`, seguida del número en
  cuestión. EL objetivo pasará a ser demostrar que ese número cumple la propiedad
  deseada."
  Hint (hidden := true) "Puesto que `d c {x} < r`, `r - (d c {x}) > 0` "
  use r - (d c x)

  Hint (hidden := true) "Si tienes un objetivo formado por la conjunción
  de dos afirmaciones, `constructor` lo separará en dos objetivos."
  constructor

  Hint (hidden := true) "Recuerda que para demostrar este tipo de (des)igualdades,
  la táctica `linarith` puede ser útil."
  linarith

  Hint "La forma de ver que un conjunto está contenido en otro, es tomar
  un elemento arbitrario del primero y ver que está en el segundo."
  Hint (hidden := true) " Para tomar un elemento arbitrario, puedes usar
  la táctica `intro`."
  intro z
  Hint (hidden := true) "Ahora, para demostrar una implicación, `intro`
  introducirá el antecedente y sólo tendrás que demostrar el consecuente."
  intro hz

  Hint "Ahora tendrás que desarrollar lo que significa estar en una bola."
  Hint (hidden := true) "Eso se puede hacer con `rw [def_bola]`"
  rw [def_bola]

  Hint "Análogamente, tendrás que hacerlo en la hioótesis `{hz}`"
  rw [def_bola] at hz

  Hint  "Como en el nivel anterior, tienes que introducir
  una hipótesis que refleje el hecho de que se cumple la desigualdad triangular."
  Hint (hidden := true) "Esto se hacia con `have htr := d4 c x z`"
  have htr := d4 c x z
  linarith
