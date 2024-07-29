import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Game.Metadata
import GameServer.Commands


World "EspaciosMetricos"
Level 1

Title "Distancias"

Introduction "En este nivel veremos la definición de distancia y espacio métrico.

Un *espacio métrico* es un conjunto $X$ junto con una aplicación $d:X × X → ℝ$ tal que:

d1: $d(x,x) = 0 ∀ x ∈ X$

d2: $d(x,y) = 0 → x = y ∀ x,y ∈ X $

d3: $d(x,y) = d(y,x) ∀ x,y ∈ X$

d4: $d(x,z) ≤ d(x,y) + d(y,z) ∀ x,y,z ∈ X$
"

class espacio_metrico (X : Type) where
  d : X → X → ℝ
  d1 : ∀ (x : X), d x x = 0
  d2 : ∀ (x y : X), d x y = 0 → x = y
  d3 : ∀ (x y : X), d x y = d y x
  d4 : ∀ (x y z : X), d x z ≤ d x y + d y z

open espacio_metrico

variable {X  : Type} [espacio_metrico X]

/--`rw [regla] (at h)` usa la afirmación `regla` para reescribir el objetivo, o la hipótesis h.

Se puede reescribir usando la regla en sentido contrario usando `rw [← regla]`. El símbolo `←` se
puede obtener tecleando `\<-`.
-/
TacticDoc rw

/--Intenta resolver el objetivo aplicando reglas de aritmética lineal a las hipótesis.-/
TacticDoc linarith

/--`have h : hip` añade una nueva hipótesis h, y un nuevo objetivo para demostrarla.
`have h := proof` añade la hipótesis cuya validez está garantizada por la prueba dada.

Puedes crear la prueba "al vuelo" aplicando un teorema a objetos e hipótesis. Es decir,
si tienes una hipótesis `h : ∀ (a : X), P a → Q a`, un objeto `x : X` y una hipótesis
`hx : P x`, `have hn := h x hx` añadirá una nueva hipótesis `hn : Q x`. Si no tuvieras
la hipótesis `hx : P x`, puedes aplicarla dejando pendiente demostrarla:
`have hn := h x ?_` añadirá la hipótesis `hn : Q x` y por otro lado añadirá un nuevo objetivo
en el que hay que demostrar `P x`.

Si alguno de los parámetros que se pasan a `have` se puede deducir de los otros, se puede
omitir poniendo `_` en su lugar. Por ejemplo, si tenemos `h : ∀ x  : X, P x → Q x`,
`a : X` y `ha : P a`, podemos usar `have h2 := h _ ha` y Lean deducirá automáticamente
que el hueco ocupado por `_` debe ser `a`.
-/
TacticDoc «have»



/--
Un espacio métrico en un tipo `X` está formado por una aplicación `d` y las propiedades
`d1` `d2` `d3` `d4`.
  -/
DefinitionDoc espacio_metrico as "espacio_metrico"

/--
$∀ (x : X), d x x = 0$
-/
DefinitionDoc espacio_metrico.d1 as "d1"

/--
$∀ (x y : X), d x y = 0 → x = y$
-/
DefinitionDoc espacio_metrico.d2 as "d2"

/--
$∀ (x y : X), d x y = d y x$
-/
DefinitionDoc espacio_metrico.d3 as "d3"

/--
$∀ (x y z : X), d x z ≤ d x y + d y z$
-/
DefinitionDoc espacio_metrico.d4 as "d4"


TheoremTab "Espacios Métricos"


/--
`d_nonneg` es la prueba de que $0 ≤ d x y$.
-/
TheoremDoc d_nonneg as "d_nonneg" in "Espacios Métricos"


NewTactic rw linarith «have»
-- NewLemma Nat.add_comm Nat.add_assoc
NewDefinition espacio_metrico espacio_metrico.d1 espacio_metrico.d2 espacio_metrico.d3 espacio_metrico.d4


/--
La distancia entre dos puntos es no negativa.
-/
Statement d_nonneg (x y : X): 0 ≤ d x y := by
  Hint "Puedes usar `have h := d4 x y x` para añadir la hipótesis de la desigualdad triangular."
  have h := d4 x y x
  Hint "La táctica `rw [d1 x] at h` usa la propiedad `d1` para reescribir la hipóetsis `h`."
  rw [d1 x] at h
  Hint "La táctica `rw [d3 y x] at h` usa la simetría de `d` para reescribir la hipóetsis `h`."
  rw [d3 y x] at h
  Hint "Ahora ya tenemos una desigualdad que se puede demostrar por aritmética lineal, podemos usar la táctica `linarith`."
  linarith

Conclusion "Enhorabuena, has realizado tu primera demostración."

/- Use these commands to add items to the game's inventory. -/
