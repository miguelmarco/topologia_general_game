import Game.Levels.Numerabilidad.IAN

World "Numerabilidad"
Level 2
Title "Límites."

Introduction "
Una *sucesión* en un espacio topológico `X`  es una
aplicación `s : ℕ → X`.

Un punto `x`  es un *límite* de una sucesión
`s` si `∀ U, entorno x U, ∃ n0, ∀ n ≥ n0, s n ∈ U`.

Una sucesión `s'`  es una *subsucesión* de `s` si
existe una aplicación monótona `f : ℕ → ℕ` tal que
`s' = s ∘ s`.


Un teorema auxiliar que vamos a necesitar es `subsucesion_creciente`, que dice
que si `f : ℕ → ℕ` es una aplicación creciente, entonces para todo `n`, se tiene que
`f n ≥ n`.
"

namespace topo
open topo espacio_topologico Set Function Nat
variable {X : Type} [espacio_topologico X]

/--
Si `f : ℕ → ℕ` es una aplicación creciente, entonces para todo `n`, se tiene que
`f n ≥ n`.
-/
TheoremDoc topo.subsucesion_creciente as "subsucesion_creciente" in "Numerabilidad"

theorem subsucesion_creciente {f : ℕ → ℕ } (h : ∀ n m, n < m → f n < f m) (n : ℕ) :
    f n ≥ n := by
  induction n
  · simp only [zero_eq, ge_iff_le, _root_.zero_le]
  · have haux : f (n_1 + 1) > f n_1
    · apply h
      linarith
    linarith

def limite (s : ℕ → X) (x : X) := ∀ U ∈ abiertos, x ∈ U →   ∃ (n0 : ℕ ), ∀ n ≥ n0 ,  (s n) ∈ U

def aglomeracion (s : ℕ → X) (x : X):= ∀ U ∈ abiertos, x ∈ U →  ∀ n0, ∃ n ≥ n0, s n ∈ U

/--
Dada una sucesión `s : ℕ → X` en un espacio topológico `X`,
un punto `x` se dice *límite* de `s`  si para todo abierto
que contenga a `x`, existe un un `n₀` tal que `∀ n ≥ n₀, s n ∈ U`.
-/
DefinitionDoc limite as "límite"

/--
Dada una sucesión `s : ℕ → X` en un espacio topológico `X`,
un punto `x` se dice que es *punto de aglomeración* de `s`  si para todo abierto
que contenga a `x`, y para todo `n₀` existe  `n ≥ n₀` tal que
`s n ∈ U`.
-/
DefinitionDoc aglomeracion as "aglomeración"


def subsucesion (s1 : ℕ → X) ( s2 : ℕ → X) := ∃ f : ℕ → ℕ, (∀ n m, n < m → f n < f m) ∧ s2 = s1 ∘ f


/--
Una sucesión `s'`  es una *subsucesión* de `s` si
existe una aplicación monótona `f : ℕ → ℕ` tal que
`s' = s ∘ s`.
-/
DefinitionDoc subsucesion as "subsucesión"


NewDefinition limite aglomeracion subsucesion

theorem def_limite (s : ℕ → X) (x : X): limite s x ↔  ∀ U ∈ abiertos, x ∈ U →   ∃ (n0 : ℕ ), ∀ n ≥ n0 ,  (s n) ∈ U := by
  rfl


theorem def_aglomeracion  (s : ℕ → X) (x : X) : aglomeracion s x ↔ ∀ U ∈ abiertos, x ∈ U →  ∀ n0, ∃ n ≥ n0, s n ∈ U := by
  rfl

theorem def_subsucesion (s1 : ℕ → X) ( s2 : ℕ → X)  : subsucesion s1 s2 ↔ ∃ f : ℕ → ℕ, (∀ n m, n < m → f n <  f m) ∧ s2 = s1 ∘ f := by
  rfl

/--
Si `X` es un espacio_topológico, `s` una sucesión
y `x` un punto, `def_limite s x` dice que  `limite s x ↔  ∀ U ∈ abiertos, x ∈ U →   ∃ (n0 : ℕ ), ∀ n ≥ n0 ,  (s n) ∈ U`.
-/
TheoremDoc topo.def_limite as "def_IAN" in "Numerabilidad"

/--
Si `X` es un espacio_topológico, `s` una sucesión
y `x` un punto, `def_aglomearcion s x` dice que  `aglomeracion s x ↔ ∀ U ∈ abiertos, x ∈ U →  ∀ n0, ∃ n ≥ n0, s n ∈ U`.
-/
TheoremDoc topo.def_aglomeracion as "def_aglomeracion" in "Numerabilidad"

/--
Si `s` y `s'` son dos sucesiones, `def_subsucesión s s'`
recoge la definición de que `s'` sea una subsucesión de `s`.

Es decir, dice que `subsucesion s s' ↔ ∃ f : ℕ → ℕ, (∀ n m, n ≤ m → f n ≤ f m) ∧ s' = s ∘ f`.
-/
TheoremDoc topo.def_subsucesion as "def_subsucesion" in "Numerabilidad"

NewTheorem topo.subsucesion_creciente topo.def_limite topo.def_aglomeracion topo.def_subsucesion

/--
Los puntos límite de una sucesión están contenidos en los puntos límite
de cualquier subsucesión suya.
-/
TheoremDoc topo.limite_subsucesion as "limite_subsucesion" in "Numerabilidad"

Statement limite_subsucesion (s1 s2 : ℕ → X) (h : subsucesion s1 s2) (x : X) :
    limite s1 x → limite s2 x := by
  Hint (hidden := true) "Puede ser útil reescribir la definición de subsucesión."
  rw [def_subsucesion] at h
  Hint (hidden := true) "Gracias a `{h}` podemos elegir una `f` y sus propiedades."
  choose f hf1  hf2 using h
  Hint (hidden := true) "Introduce el antecedente con `intro`."
  intro hx
  Hint (hidden := true) "Puedes reescribir la definición de límite en `{hx}` y
  en el objetivo."
  rw [def_limite] at hx ⊢
  Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
  intro U hU hxU
  Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
  aplicando `{hx}` a `{U}`, `{hU}` y `{hxU}`."
  have hx2 := hx U hU hxU
  Hint (hidden := true) "Puedes elegir un `n0` usando `{hx2}`."
  choose n0 hn0 using hx2
  Hint (hidden := true) "¿Qué número puedes usar?"
  use n0
  Hint (hidden := true) "Toma un `n` arbitrario con `intro`."
  intro n hn
  Hint (hidden := true) "Puedes usar `{hf2}` para reescribir el objetivo."
  rw [hf2]
  Hint (hidden := true) "Puedes aplicar `{hn0}`. Así, sólo quedará demostrar que `{f} {n0} ≥ {n0}`."
  apply hn0
  Hint (hidden := true) "Observa que `{hn}` nos dice que `{n} ≥ {n0}`, así que si
  pudieramos demostrar `{f} {n} ≥ {n}`, ya podríamos demostrar el objetivo.

  Afortunadamente, el teorema `subsucesion_creciente` nos
  dice eso mismo. Crea una nueva hipótesis con
  `have haux := subsucesion_creciente {hf1} {n}`."
  have haux := subsucesion_creciente hf1 n
  linarith


end topo
