import Game.Levels.Separacion.T1
World "Separacion"
Level 3
Title "Espacios T₂"

Introduction "Un espacio topológico se dice $T_2$ si, dados dos puntos
$x,y$, existen abiertos disjuntos $U, V$  tales que $x ∈ U$,  $y ∈ V$.

Veamos ser $T_2$ implica ser $T_1$
"

namespace topo
open topo espacio_topologico

def T2 (X : Type) [espacio_topologico X] := ∀ (x y : X), x ≠ y →  ∃ (U V  : Set X), (U ∈ abiertos ∧ V ∈ abiertos ∧  U ∩ V = ∅ ∧ x ∈ U ∧ y ∈  V)

/--
Un espacio `X` es `T2` si para todos puntos `x` e `y`, existen abiertos
disjuntos `U, V` tales que `x ∈ U` e `y ∈ V`.
-/
DefinitionDoc T2 as "T2"

NewDefinition T2

/--
Dado un espacio topológico `X`, `def_T2 X` dice que
`T2 X ↔ ∀ (x y : X), x ≠ y →  ∃ (U V  : Set X), U ∈ abiertos ∧ V ∈ abiertos ∧  U ∩ V = ∅ ∧ x ∈ U ∧ y ∉ V`
-/
TheoremDoc topo.def_T2 as "def_T2" in "lemas-definición"

theorem def_T2 (X : Type) [espacio_topologico X] : T2 X ↔ ∀ (x y : X), x ≠ y → ∃ (U V  : Set X), (U ∈ abiertos ∧ V ∈ abiertos ∧  U ∩ V = ∅ ∧ x ∈ U ∧ y ∈  V ):= by
  rfl

NewTheorem topo.def_T2

/--
Un espacio T₂ es también T₁.
-/
TheoremDoc topo.T2_T1 as "T2_T1" in "Separación"

Statement T2_T1 (X : Type) [espacio_topologico X] (h : T2 X) : T1 X := by
  Hint (hidden := true) "Puede ser útil reescribir las definiciones de T₁ y T₂"
  rw [def_T1]
  rw [def_T2] at h
  Hint (hidden := true) "Toma dos puntos arbitrarios con `intro`."
  intro x y hxy
  Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
  aplicando `{h}` a `{x}`, `{y}` y `{hxy}`."
  have h2 := h x y hxy
  Hint (hidden := true) "Gracias a `{h2}` puedes elegir dos abiertos con ciertas
  propiedades (con `choose`)."
  choose U V hU hV hUV hxU hyV using h2
  Hint (hidden := true) "¿Qué abierto puedes usar?"
  use U
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · exact hU
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · exact hxU
  · Hint (hidden := true) "Puedes suponer que `{y} ∈ {U}` (con `intro`) y
    llegar a una contradicción."
    intro hy
    Hint (hidden := true) "Ahora puedes crear una nueva hipótesis (con `have`)
    que diga que `{y}` está en `{U} ∩ {V}`."
    have haux : y ∈ U ∩ V
    · Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · exact hy
      · exact hyV
    Hint (hidden := true) "Ahora puedes usar `{hUV}` para reescribir `{haux}`."
    rw [hUV] at haux
    Hint (hidden := true) "`{haux}` es exactamente la contradicción que buscabas."
    exact haux

end topo
