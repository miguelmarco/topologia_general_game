import Game.Levels.EspaciosMetricos.Distancias

variable {X : Type} [espacio_metrico X]
open espacio_metrico

World "EspaciosMetricos"
Level 2

Title "Abiertos"

Introduction "En este nivel veremos la definición entorno, bola y abierto; y demostraremos
una relación entre estos conceptos.

Dado un punto $x$ en un espacio métrico $X$, y un número real positivo $r$, la *bola*
de centro $x$ y rdio $r$ es el conjunto de puntos del espacio que están a distancia de $x$
menor que $r$. Es decir:

$$
\\mathbb{B}(x,r) := \\{y \\in X \\mid d(x,y) < r\\}
$$

Un conjunto $E$ es un *entorno* de $x$ si hay una bola centrada en $x$, que está contenida en $E$.

Un conjunto se dice *abierto* si es entorno de todos sus puntos.

Podemos usar los siguientes resultados-definición:

Si `x` e `y` son puntos de un espacio métrico, y `r` es un número real positivo, `def_bola x y r`
dice que `y ∈ bola x r ↔ d x y < r`.

Si `x` es un punto, y `E` es un conjunto,
`def_entorno x E` dice que `entorno x E ↔ ∃ r > 0, bola x r ⊆ E`.

Si `U` es un conjunto, `def_abierto  U` dice que `abierto U ↔ ∀ x ∈ U, entorno x U`.

Estos lemas se pueden usar con la táctica `rewrite`, que permite reescribir una parte del objetivo
(o de una hipótesis) por otra equivalente.

Si la expresión `t` es una prueba de una afirmación de la forma `P ↔ Q`, entonces la táctica
`rewrite [t]` reemplazará `P` en cualquier lugar donde aparezca en la meta con `Q`. Si deseas
reemplazar `Q` con `P`, usa `rewrite [← t]`. (Escribe `\\l` para ingresar el símbolo `←`.) Para
realizar el reemplazo en una suposición `h`, usa `rewrite [t] at h`.

La táctica `rewrite` también se puede usar con ecuaciones. Si `t` es una prueba de una ecuación
`p = q`, entonces `rewrite [t]` reemplazará `p` con `q` dondequiera que aparezca, y `rewrite [← t]`
reemplazará `q` con `p`.

Para realizar múltiples reemplazos, uno después de otro, coloca una lista de pruebas dentro de los corchetes, así:
`rewrite [t1, t2]`.
"

def bola (x : X) (r : ℝ ) := { y | d x y < r}

/--
Dado un punto $x$ en un espacio métrico $X$, y un número real positivo $r$, la *bola*
de centro $x$ y rdio $r$ es el conjunto de puntos del espacio que están a distancia de $x$
menor que $r$. Es decir:

$$
\\mathbb{B}(x,r) := \\{y \\in X \\mid d(x,y) < r\\}
$$
-/
DefinitionDoc bola as "bola"


LemmaTab "lemas-definición"

lemma def_bola (x y : X) (r : ℝ ) : y ∈ bola x r ↔ d x y < r := by rfl

/--
`bola_def x y r ` es la prueba de que $y ∈ \\mathbb{B}(x,r) \\iff d(x,y) < r$
-/
LemmaDoc def_bola as "def_bola" in "lemas-definición"


def entorno (x : X) (E : Set X) := ∃ r > 0, bola x r ⊆ E

/--
Un conjunto $E$ es un *entorno* de $x$ si hay una bola centrada en $x$, que está contenida en $E$.
-/
DefinitionDoc entorno as "entorno"


lemma def_entorno  (x : X) (E : Set X) : entorno x E ↔ ∃ r > 0, bola x r ⊆ E := by rfl

/--
`def_entorno x E` es la prueba de que `entorno x E ↔ ∃ r > 0, bola x r ⊆ E`
-/
LemmaDoc def_entorno as "def_entorno" in "lemas-definición"


def abierto (U : Set X) := ∀ x ∈ U, entorno x U

/--Un conjunto $U$ es abierto si es entorno de todos sus puntos-/
DefinitionDoc abierto as "abierto"


lemma def_abierto (U : Set X) : abierto U ↔ ∀ x ∈ U, entorno x U  := by rfl

/--
`def_abierto U` es la prueba de que `abierto U ↔ ∀ x ∈ U, entorno x U`.
-/
LemmaDoc def_abierto as "def_abierto" in "lemas-definición"




/--
Si el objetivo es de la forma `∃ (x : X), P x`, donde `P` es una cierta propiedad
que pueden cumplir los términos del tipo `X`; e `y` es un término concreto
de tipo `X`, la táctica `use y` cambiará el objetivo a demostrar `P y`.
-/
TacticDoc use

NewTactic use

/--
Las bolas son conjuntos abiertos
-/
LemmaDoc bola_abierta as "bola_abierta" in "Espacios Métricos"


/--Las bolas son conjuntos abiertos-/
Statement bola_abierta (c : X) (r : ℝ ) (hr : r > 0) : abierto (bola c r) := by
  Hint "Podemos empezar reescribiendo la definición de ser un conjunto abierto."
  Hint (hidden := true) "`rw [deb_abierto]` cambiará la afirmación de que la bola es un conjunto
   abierto por su definición"
  rw [def_abierto]
  Hint "Como hay que demostrar que algo se cumple para todo `x`, habrá que tomar un `x` y demostrarlo
    para él."
  Hint (hidden := true) "Tecleando `intro x` tomaremos un `x` cualquiera."
  intro x
  Hint "Ahora hay que demostrar una implicación, así que habrá que asumir la hipótesis"
  Hint (hidden := true) "`intro h` asumirá la hipótesis"
  intro h
  Hint "Sería útil desarrollar la noción de entorno"
  Hint (hidden := true) "`rewrite def_entorno` aplicará el resultado que afirma
  la definición de entorno."

  rewrite [def_entorno]
  Hint  (hidden := true) "`rewrite [def_bola] at h` aplicará el resultado que
  afirma la definición de bola en la hipótesis `h`."

  rewrite [def_bola] at h
  Hint "Ahora tienes que demostrar que existe un número real que cumple una cierta
  propiedad. ¿Sabes cual puede ser?.

  Una vez  lo tengas claro, utiliza la táctica `use`, seguida del número en
  cuestión. EL objetivo pasará a ser demostrar que ese número cumple la propiedad
  deseada."
  use r - (d c x)

  constructor

  linarith

  intro z hz

  rewrite [def_bola] at *

  have haux := d4 c x z
  linarith
