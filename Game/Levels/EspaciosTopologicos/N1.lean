import Game.Levels.EspaciosTopologicos.Entornos
open Set espacio_topologico



World "EspaciosTopologicos"
Level 8
Title "Propiedades de entornos 1"

Introduction "En los siguientes niveles vamos a ver ciertas propiedades
que cumplen las familias de entornos de cada punto en un espacio
topológico. Posteriormente veremos que unas familias que cumplan
esas propiedades, de hecho, determinan una topología.

En particular, si tenemos un conjunto ambiente $X$, y una aplicación
$\\mathcal{E}$ que a cada punto $x$ le asigna una familia de subconjuntos
$\\mathcal{E}(x)$, definimos las siguientes propiedades que puede cumplir.

- `N1` : $\\forall x \\in X, \\mathcal{E}(x) \\neq \\emptyset$.
- `N2` : $\\forall N \\in \\mathcal{E}(x), x ∈ N$
- `N3` : $\\forall N_1, N_2 \\in \\mathcal{E}(x), N_1, \\cap  N_2 \\in \\mathcal{E}(x)$
- `N4` : $\\forall N \\in \\mathcal{E}(x), \\forall A, N \\subseteq A \\Rightarrow  A \\in \\mathcal{E}(x)$
- `N5` : $\\forall N \\in \\mathcal{E}(x), \\exists N' \\in \\mathcal{E}(x), \\forall y \\in N', N \\in \\mathcal{E}(y)$
"

def N1 (X : Type) (E : X → Set (Set X)) := ∀ (x : X) , ∃ (N : Set X) , N ∈ E x

/--
Dada una familia de conjuntos `E x` para cada punto de un espacio, decimos
que cumple `N1` si para cualquier punto, la familia es no vacía.
-/
DefinitionDoc N1 as "N1"

def N2 (X : Type) (E : X → Set (Set X)) := ∀ x, ∀ N ∈ E x, x ∈ N

/--
Dada una familia de conjuntos `E x` para cada punto de un espacio, decimos
que cumple `N2` si todos los elementos de `E x` contienen a `x`.
-/
DefinitionDoc N2 as "N2"

def N3 (X : Type) (E : X → Set (Set X)) := ∀ (x : X), ∀ N1 ∈ (E x), ∀  N2 ∈ (E x), N1 ∩ N2 ∈ E x

/--
Dada una familia de conjuntos `E x` para cada punto de un espacio, decimos
que cumple `N3` si para dos conjuntos de `N1, N2 ∈ E x`, se cumple que `N1 ∩ N2 ∈ E x`.
-/
DefinitionDoc N3 as "N3"

def N4 (X : Type) (E : X → Set (Set X)) := ∀ x, ∀ N ∈ (E x), ∀ N2, N ⊆ N2 → N2 ∈ E x
/--
Dada una familia de conjuntos `E x` para cada punto de un espacio, decimos
que cumple `N4` si cualquier superconjunto de un elemento de `E x` está en `E x`.
-/
DefinitionDoc N4 as "N4"

def N5 (X : Type) (E : X → Set (Set X)) := ∀ x, ∀ N ∈ E x, ∃ N' ∈ E x, ∀ y ∈ N', N ∈ E y

/--
Dada una familia de conjuntos `E x` para cada punto de un espacio, decimos
que cumple `N3` si para dos conjuntos de `N1, N2 ∈ E x`, se cumple que `N1 ∩ N2 ∈ E x`.
-/
DefinitionDoc N5 as "N5"

NewDefinition N1 N2 N3 N4 N5

/--
Las familias de los entornos de cada punto en un espacio topológico cumplen `N1`.
-/
TheoremDoc entornos_N1 as "entornos_N1" in "Espacios Topológicos"

Statement entornos_N1 (X : Type) [espacio_topologico X] : ∀ x : X, ∃ N, entorno x N := by
  Hint (hidden := true) "Puesto que el objetivo es una afirmación universal,
  podemos tomar un punto genérico con `intro x`."
  intro x
  Hint (hidden := true) "Recuerda que para demostrar que existe un cierto objeto
  con una propiedad, lo habitual es dar un concreto con `use`."
  Hint (hidden := true) "¿Qué conjunto puedes asegurar que contiene a `{x}` y a su vez
  un aboierto?"
  Hint (hidden := true) "Prueba con `use univ`."
  use univ
  Hint (hidden := true) "Puede ser útil reescribir lo que significa ser
  entorno de un punto con `rw [def_entorno]` o `unfold entorno`."
  rw [def_entorno]
  Hint (hidden := true) "Ahora hay que dar el abierto intermedio entre `{x}`
  y `univ`. ¿Cual puede ser?"
  Hint (hidden := true) "Usa `use univ`."
  use univ
  Hint (hidden := true) "Para separar un objetivo construido con varias
 partes, usa `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Recuerda que el objetivo es exactamente lo que
    afirma `abierto_total`."
    exact abierto_total
  Hint (hidden := true) "Hay que volver a separar en partes con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Esto es cierto trivialmente."
    trivial
  · Hint (hidden := true) "Esto es cierto trivialmente."
    trivial
