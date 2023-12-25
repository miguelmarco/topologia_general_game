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
"

def bola (x : X) (r : ℝ ) := { y | d x y < r}

DefinitionDoc bola as "bola"
"
Dado un punto $x$ en un espacio métrico $X$, y un número real positivo $r$, la *bola*
de centro $x$ y rdio $r$ es el conjunto de puntos del espacio que están a distancia de $x$
menor que $r$. Es decir:

$$
\\mathbb{B}(x,r) := \\{y \\in X \\mid d(x,y) < r\\}
$$
"

lemma bola_def (x y : X) (r : ℝ ) : y ∈ bola x r ↔ d x y < r := by rfl

LemmaDoc bola_def as "bola_def" in "bola_def"
"
`bola_def x y r ` es la prueba de que $y ∈ \\mathbb{B}(x,r) \\iff d(x,y) < r$
"

def entorno (x : X) (E : Set X) := ∃ r > 0, bola x r ⊆ E

DefinitionDoc entorno as "entorno"
"
Un conjunto $E$ es un *entorno* de $x$ si hay una bola centrada en $x$, que está contenida en $E$.
"
