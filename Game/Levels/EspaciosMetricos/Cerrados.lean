import Game.Levels.EspaciosMetricos.Abiertos

variable {X : Type} [espacio_metrico X]
open espacio_metrico

World "EspaciosMetricos"
Level 3

Title "Cerrados"

Introduction "En este nivel trataremos la noción de cerrado métrico.

En un espacio métrico $X$, un subconjunto $C \\subseteq X$ se dice *cerrado métrico*
si su complementario es abierto.

El lema `def_cerrado_metrico` dice exactamente eso: que `cerrado_metrico C ↔ abierto_metrico Cᶜ`.
"

def cerrado_metrico (C : Set X) := abierto_metrico Cᶜ

/--
Si $X$ es un espacio métrico, y $C\subseteq X$; decimos que $C$ es *cerrado métrico* si
su complementario es abierto.
-/
DefinitionDoc cerrado_metrico as "cerrado_metrico"

lemma def_cerrado_metrico (C : Set X) : cerrado_metrico C ↔ abierto_metrico Cᶜ := by rfl

/--
`def_cerrado_metrico C` es una prueba de `cerrado_metrico C ↔ abierto_metrico Cᶜ`.
-/
TheoremDoc def_cerrado_metrico as "def_cerrado_metrico" in "lemas-definición"

def disco (x : X) (r : ℝ ) := { y  | d x y ≤ r}

/--
Dado un punto $x$ en un espacio métrico $X$, y un número real positivo $r$, el *disco*
de centro $x$ y radio $r$ es el conjunto de puntos del espacio que están a distancia de $x$
menor o igual que $r$. Es decir:

$$
\mathbb{D}(x,r) := \{y \in X \mid d(x,y) ≤ r\}
$$
-/
DefinitionDoc disco as "disco"

lemma def_disco (x y: X) (r : ℝ) : y ∈ disco x r ↔  d x y ≤ r := by rfl

/--
`disco_def x y r ` es la prueba de que $y ∈ \mathbb{D}(x,r) \iff d(x,y) ≤ r$
-/
TheoremDoc def_disco as "def_disco" in "lemas-definición"


/--
`simp` aplica algunos lemas de equivalencia para simplificar expresiones. Se pueden dar
lemas adicionales para que los use en la simplificación, similarmente a la táctica `rw`.

`simp [regla]` simplifica usando `regla`.

`simp [regla] at h` simplifica la hipótesis `h` usando la regla.

También se puede usar sin pasar reglas.
-/
TacticDoc simp

NewTactic simp
NewTheorem def_cerrado_metrico def_disco
NewDefinition cerrado_metrico disco

/--
Los discos son cerrados métricos
-/
TheoremDoc disco_cerrado as "disco_cerrado" in "Espacios Métricos"



/--Los discos son cerrados métricos-/
Statement disco_cerrado (c : X) (r : ℝ )  : cerrado_metrico (disco c r) := by
  Hint (hidden := true) "Puedes empezar usando la definición de cerrado métrico para reescribir el objetivo."
  rw [def_cerrado_metrico]
  Hint (hidden := true) "Análogamente, puedes usar la definición de abierto métrico."
  rw [def_abierto_metrico]
  Hint "Como debes demostrar que cierta propiedad se cumple para todo elemento, puedes tomar uno arbitrario."
  Hint (hidden := true) "Se puede tomar un elemento arbitrario con `intro x`"
  intro x
  Hint "Ahora puedes introducir el antecedente del objetivo como una nueva hipótesis."
  Hint (hidden := true) "Para introducir el antecedente del objetivo como nueva hipótesis, puedes usar `intro hx`."
  intro hx
  Hint "Que `{x}` esté en el complementario del disco es una expresión un poco rebuscada. La podemos simplificar
  con `simp [def_disco] at {hx}`."
  simp [def_disco] at hx
  Hint "Como queremos demostrar que un cierto conjunto es entorno métrico de un punto, hay que dar el radio
  de una bola centrada en el punto y contenida en el conjunto. Piensa cual puede ser."
  Hint (hidden := true) "Prueba con la diferencia dentre la distancia de `c` a `{x}`; `use d c {x}` - r."
  use d c x - r
  Hint (hidden := true) "Como hay que demostrar una conjunción, `fconstructor` nos permite separarla en dos
  sub-objetivos."
  fconstructor
  Hint (hidden := true) "esta desigualdad se demuestra por aritmética lineal : `linarith`."
  linarith
  Hint (hidden := true) "Para demostrar que un conjunto está contenido en otro, debes tomar un elemento arbitrario del primero
  y ver que está en el segundo."
  intro y
  Hint (hidden := true) "Como antes, puedes introducir el antecedente de la implicación que quieres demostrar
  como una nueva hipótesis."
  intro hy
  Hint "Ahora deberíamos ver qué significa que `{y}` esté en una bola. Prueba a simplificar esa expresión con
  `simp [def_bola] at {hy}`."
  rw [def_bola] at hy
  Hint "También tenemos que ver qué significa estar en el complementario del disco: `simp [def_disco]`."
  simp [def_disco]
  Hint "Parece que nos hará falta usar alguna desigualdad más. Piensa cual es la que necesitas, y cómo la puedes obtener."
  Hint (hidden := true) "Necesitas la desigualdad triangular aplicada a  `c`, `{y}` y `{x}`: `have htriang := d4 c {y} {x}`."
  have htriang := d4 c y x
  Hint "Desgraciadamente, alguna de las distancias que estamos usando está expresada de dos maneras distintas.
  ¿Cómo podemos arreglarlo?"
  Hint (hidden := true) "Prueba a reescribir la distancia entre `{x}` e {y}` en `{hy}`: `rw [d3  {x} {y}] at {hy}`."
  Branch
    rw [d3  x y] at hy
    Hint "Y ahora ya sí que basta aplicar aritmética lineal."
    linarith
  rw [d3 y x] at htriang
  Hint "Y ahora ya sí que basta aplicar aritmética lineal."
  linarith
