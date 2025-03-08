import Game.Levels.Separacion.SepararSiiClausura

World "Separacion"
Level 2
Title "Espacios T₁"

Introduction "Un espacio topológico se dice $T_1$ si, dados dos puntos
$x,y$, existe un abierto $U$ que contiene a $x$ pero no a $y$.

Veamos que eso es equivalente a que los conjuntos unipuntuales sean
cerrados.

"

namespace topo
open topo espacio_topologico

def T1 (X : Type) [espacio_topologico X] := ∀ (x y : X), x ≠ y →  ∃ U ∈ abiertos, (x ∈ U ∧ y ∉ U)

/--
Un espacio `X` es `T1` si para todos puntos `x` e `y`, existe un abierto `U`
tal que `x ∈ U` e `y ∉ U`.
-/
DefinitionDoc T1 as "T1"

NewDefinition T1

/--
Dado un espacio topológico `X`, `def_T1 X` dice que
`T1 X ↔ ∀ (x y : X), ∃ U ∈ abiertos, x ∈ U ∧ y ∉ U`
-/
TheoremDoc topo.def_T1 as "def_T1" in "lemas-definición"

theorem def_T1 (X : Type) [espacio_topologico X] : T1 X ↔ ∀ (x y : X), x ≠ y →  ∃ U ∈ abiertos, x ∈ U ∧ y ∉ U := by
  rfl

NewTheorem topo.def_T1

/--
Un espacio topológico es `T1` si y solo si los conjuntos
unipuntuales son cerrados.
-/
TheoremDoc topo.caracterizacion_T1 as "caracterizacion_T1" in "Separación"

Statement caracterizacion_T1 (X : Type) [espacio_topologico X] : T1 X ↔ ∀ (x : X), {x} ∈ cerrados := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h x
    Hint (hidden := true) "Será útil reescribir la definición de cerrado y de espacio T1."
    rw [def_T1] at h
    rw [def_cerrado]
    Hint (hidden := true) "En este caso, será útil reescribir el objetivo como
    que el conjunto es entorno de todos sus puntos."
    rw [abierto_sii_entorno]
    Hint (hidden := true) "Toma un punto arbitrario con `intro`,"
    intro y hy
    Hint (hidden := true) "Puedes obtener una nueva hipótesis
    (con `have`) aplicando `{h}` a `{y}`, `{x}` y `{hy}`."
    have h2 := h y x hy
    Hint (hidden := true) "`{h2}` te asegura que existen ciertos abiertos.
    Elige uno con `choose`."
    choose U hU hyU hxU using h2
    Hint (hidden := true) "Si no ves claro qué hacer, reescribe la definición
    de entorno."
    rw [def_entorno]
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hyU
    · Hint (hidden := true) "Será útil simplificar el objetivo."
      simp only [Set.subset_compl_singleton_iff]
      exact hxU
  · Hint (hidden := true) "Introduce una hipótesis con `intro`."
    intro h
    Hint (hidden := true) "Puede ser útil reescribir la definición de espacio T1."
    rw [def_T1]
    Hint (hidden := true) "Toma puntos arbitrarios con `intro`."
    intro x y hxy
    Hint (hidden := true) "Piensa qué abierto puedes usar. Recuerda que debe ser
    un abierto que no contenga a `{y}`, y lo que sabes es que los conjuntos
    de un solo punto son cerrados."
    use {y}ᶜ
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Fíjate en que el objetivo es un caso particular de `{h}`."
      apply h
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Si no lo ves claro, prueba a simplificar el objetivo."
      exact hxy
    · Hint (hidden := true) "Prueba a simplificar el objetivo"
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false, not_false_eq_true]


end topo
