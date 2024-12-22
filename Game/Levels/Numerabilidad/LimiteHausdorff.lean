import Game.Levels.Numerabilidad.AglomeracionContinua

World "Limites"
Level 8
Title "Límites en espacios de Hausdorff."

Introduction "
Un espacio topologico se dice de `Hausdorff` si, dados dos puntos
distintos `x, y`,  existen entornos `U` y `V` de `x` e `y` respectivamente,
tales que `U ∩ V = ∅`.
"

def Hausdorff (X : Type) [topo.espacio_topologico X] := ∀ (x y : X), x ≠ y → ∃ (U V : Set X), topo.entorno x U ∧ topo.entorno y V ∧ U ∩ V = ∅


namespace topo
open topo espacio_topologico Set Function Nat
variable {X Y: Type}  [espacio_topologico X] [espacio_topologico Y]

/--
Un espacio topologico se dice de `Hausdorff` si, dados dos puntos
distintos `x, y`,  existen entornos `U` y `V` de `x` e `y` respectivamente,
tales que `U ∩ V = ∅`.
-/
DefinitionDoc Hausdorff as "Hausdorff"


/--
Dado un espacio topológico `X`, `def_hausdorff X` dice que `Hausdorff X ↔  ∀ (x y : X), x ≠ y → ∃ (U V : Set X), topo.entorno x U ∧ topo.entorno y V ∧ U ∩ V = ∅`.
-/
TheoremDoc topo.def_hausdorff as "def_hausdorff" in "Limites"

theorem def_hausdorff : Hausdorff X ↔  ∀ (x y : X), x ≠ y → ∃ (U V : Set X), topo.entorno x U ∧ topo.entorno y V ∧ U ∩ V = ∅ := by
  rfl

NewTheorem topo.def_hausdorff

/--
En un espacio de Hausdorff, las sucesiones convergentes tienen
límite único.
-/
TheoremDoc topo.limite_unico as "limite_unico" in "Limites"

Statement limite_unico {s : ℕ → X} (hX : Hausdorff X)  (x y : X) (hx : limite s x ) (hy : limite s y) :
    x = y := by
  Hint (hidden := true) "Será útil reescribir la definición de espacio
  Hausdorff."
  rw [def_hausdorff] at hX
  Hint (hidden := true) "Como `{hx}` se puede usar cuando tengamos
  dos puntos distintos, podemos suponer que `{x}` e `{y}` son distintos
  y llegar a una contradicción: usa `by_contra`."
  by_contra hneg
  Hint (hidden := true) "Ahora podemos obtener una nueva hipótesis (con `have`)
  aplicando `{hX}` a `{x}`, `{y}` y `{hneg}`."
  have hn := hX x y hneg
  Hint (hidden := true) "Gracias a `{hn}`, puedes elegir
  unos entornos disjuntos de `{x}` e `{y}`."
  choose U V hU hV hUV using hn
  Hint (hidden := true) "Ahora puede ser útil reescribir la definición de
  límite en `{hx}` y `{hy}`."
  rw [def_limite] at hx hy
  Hint (hidden := true) "`{hU}` y `{hV}` aseguran que existen ciertos
  abiertos. Puedes elegirlos."
  choose U' hU' hxU' hU'U using hU
  choose V' hV' hyV' hV'V using hV
  Hint (hidden := true) "Ahora puedes usar `{hx}` con `{U'}` para obtener
  una nueva hipótesis."
  have hx2 := hx U' hU' hxU'
  Hint (hidden := true) "Puedes hacer análogamente con `{hy}`."
  have hy2 := hy V' hV' hyV'
  Hint (hidden := true) "Gracias a `{hx2}`, puedes elegir un natural."
  choose nx hnx using hx2
  Hint (hidden := true) "Análogamente con `{hy2}`."
  choose ny hny using hy2
  Hint (hidden := true) "Ahora, dependiendo de si `{nx}` es menor
  que `{ny}` o no, habrá que usar uno o el otro.

  Teclea `by_cases  hcas : {nx} < {ny}`."
  by_cases hcas : nx < ny
  · Hint (hidden := true) "En este caso, necesitamos ver que `{s} {ny} ∈ {U} ∩ {V}`.

    Crea un objetivo para demostrarlo con `have haux : {s} {ny} ∈ {U} ∩ {V}`."
    have haux : s ny ∈ U ∩ V
    · Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Se puede aplicar `{hU'U}`."
        apply hU'U
        Hint (hidden := true) "Se puede aplicar `{hnx}`."
        apply hnx
        Hint (hidden := true) "Esto se puede probar con aritmética lineal."
        linarith
      · Hint (hidden := true) "Se puede aplicar `{hV'V}`."
        apply hV'V
        Hint (hidden := true) "Se puede aplicar `{hny}`."
        apply hny
        Hint (hidden := true) "Esto se puede ver usando aritmética lineal."
        linarith
    Hint (hidden := true) "Ahora puedes reescribir `{hUV}` en `{haux}`."
    rw [hUV] at haux
    Hint (hidden := true) "La contradicción ahora es exactamente `{haux}`."
    exact haux
  · Hint (hidden := true) "En este caso, lo que necesitamos es ver que
    `{s} {nx} ∈ {U} ∩ {V}`."
    have haux : s nx ∈ U ∩ V
    · Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Aplica `{hU'U}`."
        apply hU'U
        Hint (hidden := true) "Aplica `{hnx}`."
        apply hnx
        Hint (hidden := true) "Esto se demuestra con aritmética lineal."
        linarith
      · Hint (hidden := true) "Aplica `{hV'V}`."
        apply hV'V
        Hint (hidden := true) "Aplica `{hny}`."
        apply hny
        Hint (hidden := true) "Esto se demuestra por aritmética lineal."
        linarith
    Hint (hidden := true) "Reescribe `{hUV}` en `{haux}`."
    rw [hUV] at haux
    Hint (hidden := true) "Ahora la contradicción viene con `{haux}`"
    exact haux


end topo
