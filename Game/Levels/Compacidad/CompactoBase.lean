import Game.Levels.Cocientes.IdentificacionSiiHomeomorfismo

World "Compacidad"
Level 1
Title "Compacidad en términos de bases"

Introduction "Antes de empezar en este mundo, vamos a introducir una serie de
definiciones, y sus correspondientes teoremas. En un espacio topológico
`X`, dados un conjunto `A` y una familia de subconjuntos `ℱ`:

- `recubrimiento A ℱ` se define como `A ⊆ ⋃₀ ℱ`.
- `def_recubrimiento A ℱ` dice que `recubrimiento A ℱ ↔ A ⊆ ⋃₀ ℱ`.
- `compacto A` se define como `∀ ℱ ⊆ abiertos, recubrimiento A ℱ → ∃ S ⊆ ℱ, (Set.Finite S ∧ recubrimiento A S)`.
- `def_compacto` es el teorema que afirma la definición anterior.
- `espacio_compacto X` se define como `compacto univ`.
- `def_espacio_compacto` es el teorema que afirma la definición anterior.



Veamos que la compacidad se puede
plantear en términos de cubrimientos de abiertos básicos.

En esta demostración, tendremos en algún momento que elegir un
elemento con ciertas propiedades para cada conjunto `S : Set X`
de una cierta familia `F : Set (Set X)`,
sabiendo que para cada `S ∈ F`, existe un elemento `x ∈ S` como el que queremos.
Recuerda que, en esa situación, la táctica `choose!` te da una *función de elección*
`f : Set X → X`,
que te da un elemento para cada conjunto, y te asegura que si `S ∈ F`, el elemento `f S`
cumple la condición requerida.

"

namespace topo
open espacio_topologico topo Set Set.Finite

variable {X : Type} [espacio_topologico X]

/--
Dado un conjunto `A`, una familia `ℱ` se dice que es un
recubrimiento de `A` si `A ⊆ ⋃₀ ℱ`.
-/
DefinitionDoc recubrimiento as "recubrimiento"

def recubrimiento (A : Set X) (ℱ : Set (Set X)) := A ⊆ ⋃₀ ℱ

/--
En un espacio topológico, un conjunto `A` se dice *compacto*
si todo recubrimiento de `A` formado por abiertos tiene un
subrecubrimiento finito.
-/
DefinitionDoc compacto as "compacto"

def compacto (A : Set X) := ∀ ℱ ⊆ abiertos, recubrimiento A ℱ → ∃ S ⊆ ℱ, (Set.Finite S ∧ recubrimiento A S)

/--
Un espacio topológico se dice compacto si el conjunto
total es compacto.
-/
DefinitionDoc espacio_compacto as "espacio_compacto"

def espacio_compacto (X : Type) [espacio_topologico X] := compacto (univ : Set X)


/--
Dado un conjunto `A` y una familia `ℱ`, `def_recubrimiento A ℱ`
dice que `recubrimiento A ℱ ↔ A ⊆ ⋃₀ ℱ`.
-/
TheoremDoc topo.def_recubrimiento  as "def_recubrimiento" in "lemas-definición"

theorem def_recubrimiento (A : Set X) (ℱ : Set (Set X)) : recubrimiento A ℱ ↔ A ⊆ ⋃₀ ℱ := by rfl

/--
Dado un conjunto `A` en un espacio topológico, `def_compacto A`
dice que `compacto A ↔ ∀ ℱ ⊆ abiertos, recubrimiento A ℱ → ∃ S ⊆ ℱ, (Set.Finite S ∧ recubrimiento A S)`.
-/
TheoremDoc topo.def_compacto as "def_compacto" in "lemas-definición"

theorem def_compacto (A : Set X) : compacto A ↔ ∀ ℱ ⊆ abiertos, recubrimiento A ℱ → ∃ S ⊆ ℱ, (Set.Finite S ∧ recubrimiento A S) := by rfl

/--
Dado un espacio topológico `X`, `def_espacio_compacto` dice que
`espacio_compacto X ↔ compacto (univ : Set X)`.
-/
TheoremDoc topo.def_espacio_compacto as "espacio_compacto" in "lemas-definición"

theorem def_espacio_compacto (X : Type) [espacio_topologico X] : espacio_compacto X ↔ compacto (univ : Set X) := by
  rfl

/-
theorem compacto_sii_parametrizado (A : Set X)  :
    compacto A ↔ ∀ (Λ : Type) (F : Λ → Set X), (∀ i, F i ∈ abiertos) →  A ⊆ ⋃ i, F i  → ∃ (S : Set Λ), Set.Finite S ∧ A ⊆ ⋃ (i ∈ S), F i := by
  fconstructor
  · intro h Λ F hF hA
    specialize h (range F) ?_ ?_
    · intro U hU
      choose i hi  using hU
      rw [← hi]
      apply hF
    · intro x hx
      specialize hA hx
      exact hA
    choose S hSF hSfin hSA using h
    change ∀ s, s ∈ S →  (∃ (l : Λ), F l = s) at hSF
    have haux : ∀ s : S, (∃ (l : Λ), F l = s)
    · rintro ⟨s,hs⟩
      apply hSF
      exact hs
    choose g hg using haux
    use range g
    fconstructor
    have haux : Finite S
    · exact hSfin
    apply Set.finite_range
    intro x hx
    specialize hSA hx
    choose U hUS hxU using hSA
    use U
    fconstructor
    fconstructor
    apply g
    fconstructor
    exact U
    exact hUS
    simp only [mem_range, exists_apply_eq_apply, iUnion_true]
    specialize hSF U hUS
    choose l hl using hSF
    specialize hg ⟨U,hUS⟩
    simp only at hg
    exact hg
    exact hxU
  · intro h
    intro F hFab hAF
    specialize h F ?_ ?_ ?_
    · rintro ⟨U,hU⟩
      exact U
    · simp only [Subtype.forall]
      exact hFab
    · simp only [iUnion_coe_set]
      intro x hx
      specialize hAF hx
      choose U hU hxU using hAF
      use U
      simp only [mem_range, hxU, and_true]
      use U
      simp only [hU, iUnion_true]
    choose S hSF hAS using h
    simp only [iUnion_coe_set] at hAS
    use {↑U | U : S}
    fconstructor
    · intro x hx
      simp only [Subtype.exists, exists_prop, exists_and_right, exists_eq_right, mem_setOf_eq] at hx
      choose x1 hx1  using hx
      exact x1
    fconstructor
    · have haux : Finite S
      · exact hSF
      apply Set.finite_range
    · intro x hx
      specialize hAS hx
      simp_all only [mem_iUnion, exists_prop, exists_and_right, Subtype.exists, exists_eq_right,
        mem_sUnion, mem_setOf_eq]
-/



NewDefinition recubrimiento compacto espacio_compacto

NewTheorem topo.def_recubrimiento topo.def_compacto topo.def_espacio_compacto

TheoremTab "Compacidad"

/--
Si `ℬ` es una base de abiertos de `X`, y `A` es un subconjunto,
`caracterizacion_compacto_base A ℬ` dice que `A` es compacto
si y solo si todo recubrimiento suyo formado por abiertos básicos,
admite un subrecubrimiento finito.
-/
TheoremDoc topo.caracterizacion_compacto_base as "caracterizacion_compacto_base" in "Compacidad"


Statement caracterizacion_compacto_base (A : Set X) (B :  Set (Set X)) (hB : base B) :
    compacto A ↔ ∀ R ⊆ B, recubrimiento A R → ∃ S, (S ⊆ R ∧  Set.Finite S ∧ recubrimiento A S) := by
  Hint (hidden := true) "Será útil reescribir `{hB}` en términos de la caracterización
  de las bases."
  rw [caracterizacion_base] at hB
  Hint (hidden := true) "Puedes separar `{hB}` en dos afirmaciones con `choose` o `cases'`."
  choose hB1 hB2 using hB
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes reescribir la definición de compacto en `{h}`."
    rw [def_compacto] at h
    Hint (hidden := true) "Toma un recubrimiento arbitrario (y sus propiedades) con `intro`."
    intro R hR hRA
    Hint (hidden := true) "Observa que lo que queremos es un caso particular
    de lo que afirma `{h}`, así que podemos aplicarlo."
    apply h
    · Hint (hidden := true) "Toma un elemento de `{R}` arbitrario con `intro`."
      intro U hU
      Hint (hidden := true) "Puedes aplicar `{hB1}`."
      apply hB1
      Hint (hidden := true) "Puedes aplicar `{hR}`."
      apply hR
      exact hU
    · exact hRA
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Será útil reescribir la definición de compacto."
    rw [def_compacto]
    Hint (hidden := true) "Toma una familia de abiertos arbitraria (y sus propiedades)
    con `intro`."
    intro F hF hAF
    Branch
      rw [def_recubrimiento] at hAF
      Hint "Observa que, para poder asegurar lo que queremos, tenemos que usar `{h}`
      de alguna forma, pero sólo podemos aplicarla a recubrimientos de `{A}`
      formados por elementos de `{B}`.  Así que tenemos que construirnos algún
      tal recubrimiento.

      La opción natural es tomar los elementos de la base que estén contenidos en
      algún elemento de `{F}`.

      Teclea `let C := \{U | U ∈ {B} ∧ ∃ V ∈ {F}, U ⊆ V }`."
    Hint "Observa que, para poder asegurar lo que queremos, tenemos que usar `{h}`
    de alguna forma, pero sólo podemos aplicarla a recubrimientos de `{A}`
    formados por elementos de `{B}`.  Así que tenemos que construirnos algún
    tal recubrimiento.

    La opción natural es tomar los elementos de la base que estén contenidos en
    algún elemento de `{F}`.

    Teclea `let C := \{U | U ∈ {B} ∧ ∃ V ∈ {F}, U ⊆ V }`."
    let C := {U | U ∈ B ∧ ∃ V ∈ F, U ⊆ V}
    Hint (hidden := true) "Para poder aplicar `{h}` a `{C}`, necesitamos
    ver que está contenido en `{B}` y que es un recubrimiento de `{A}`, así
    que vamos a crear estas dos afirmaciones (y demostrarlas, claro).

    Teclea `have hC1 : ̣{C} ⊆ {B}`."
    have hC1 : C ⊆ B
    · Hint (hidden := true) "Toma un elemento de `{C}` arbitrario con `intro`."
      intro U hU
      Hint (hidden := true) "Puedes obtener dos afirmaciones a partir de `{hU}`
      con `choose` o `cases'`."
      choose hU1 hU2 using hU
      exact hU1
    Hint (hidden := true) "Ahora teclea `have hC2 : recubrimiento {A} {C}`."
    have hC2 : recubrimiento A C
    · Hint (hidden := true) "Prueba a reescribir lo que significa ser recubrimiento
      en `{hAF}` y el objetivo."
      rw [def_recubrimiento] at hAF ⊢
      Hint (hidden := true) "Toma un elemento arbitrario de `{A}` con `intro`."
      intro x hx
      Hint (hidden := true) "Observa que puedes aplicar `{hAF}` a `{hx}`
      y obtener una nueva hipótesis (con `have`)."
      have hxA := hAF hx
      Hint (hidden := true) "Gracias a `{hxA}` puedes elegir un conjunto en `{F}`
      que contenga a `{x}` (con `choose`)."
      choose U hUF hxU using hxA
      Hint (hidden := true) "Observa que puedes aplicar `{hF}` a `{hUF}`
      y obtener una nueva hipótesis (con `have`)."
      have hUab := hF hUF
      Hint (hidden := true) "Ahora puedes aplicar `{hB2}` a `{U}`, `{hUab}`, `{x}`
      y `{hxU}` para obtener una nueva hipótesis (con `have`)."
      have haux := hB2 U hUab x hxU
      Hint (hidden := true) "Gracias a `{haux}` puedes elegir un elemento de `{B}`
      con ciertas propiedades (con `choose`)."
      choose V hVV hxV hVU using haux
      Hint (hidden := true) "El elemento de `{C}` que tienes que usar es `{V}`."
      use V
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Observa que estar `{C}` significa cumplir dos
        propiedades, así que puedes separar el objetivo en dos con `fconstructor`."
        fconstructor
        · exact hVV
        · Hint (hidden := true) "Piensa qué elemento de `{F}` tienes que usar."
          use U
      · exact hxV
    Hint (hidden := true)"Ahora puedes aplicar `{h}` a `{C}`, `{hC1}` y `{hC2}`
    para obtener una nueva hipótesis (con `have`)."
    have h2 := h C hC1 hC2
    Hint (hidden := true) "Puedes elegir un subconjunto de `{C}` con ciertas propiedades
    gracias a `{h2}` (con `choose`)."
    choose S hS1 hS2 hS3 using h2
    Branch
      rw  [def_recubrimiento] at hAF hS3 hC2
      Hint "Ahora, para cada elemento de `{S}`,
      necesitamos elegir un elmento de `{F}` que lo contenga. Antes de poder hacerlo,
      necesitamos asegurar que existen.

      Teclea `have hS : ∀ U ∈ {S}, ∃ UF ∈ {F}, U ⊆ UF`."
    Hint "Ahora, para cada elemento de `{S}`,
    necesitamos elegir un elmento de `{F}` que lo contenga. Antes de poder hacerlo,
    necesitamos asegurar que existen.

    Teclea `have hS : ∀ U ∈ {S}, ∃ UF ∈ {F}, U ⊆ UF`."
    have hS : ∀ U  ∈ S, ∃ UF ∈ F, U  ⊆ UF
    · Hint (hidden := true) "Toma un elemento arbitrario de `{S}`con `intro`."
      intro U hU
      Hint (hidden := true) "Puedes aplicar `{hS1}` a `{hU}` para obtener una nueva
      hipótesis (con `have`)."
      have hU1 := hS1 hU
      Hint (hidden := true) "Puedes usar `{hU1}` para elegir un elemento de `{B}`
      que contenga a `{U}` con `choose`."
      choose V hV1 hV2 using hU1
      Hint (hidden := true) "¿Cual es el elemento de `{F}` que tienes que usar?"
      use hV1
    Branch
      rw [def_recubrimiento] at hAF hS3 hC2
      Hint "Ahora es cuando tenemos que elegir un elemento de `{F}` por cada
      elemento de `{S}`, que lo contenga.

      Gracias a `{hS}` sabemos que existen, pero tenemos que elegir todos a la vez
      de alguna forma. Esto se hace con la táctica `choose!`, que nos dará
      una *función de elección*.

      Teclea `choose f hf1 hf2 using {hS}`."
      choose! f hf1 hf2 using hS
      Hint "Ahora gracias a la función `{f}`, ya sabemos cómo dar nuestra
      subfamilia. Concretamente las imagenes por `{f}` de los elementos de
      `{S}`. Es decir, `{f} '' {S}`.

      Teclea `use {f} '' {S}`."
    Hint "Ahora es cuando tenemos que elegir un elemento de `{F}` por cada
    elemento de `{S}`, que lo contenga.

    Gracias a `{hS}` sabemos que existen, pero tenemos que elegir todos a la vez
    de alguna forma. Esto se hace con la táctica `choose!`, que nos dará
    una *función de elección*.

    Teclea `choose f hf1 hf2 using {hS}`."
    choose! f hf1 hf2 using hS
    Hint "Ahora gracias a la función `{f}`, ya sabemos cómo dar nuestra
    subfamilia. Concretamente las imagenes por `{f}` de los elementos de
    `{S}`. Es decir, `{f} '' {S}`.

    Teclea `use {f} '' {S}`."
    use f '' S
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
      intro U hU
      Hint (hidden := true) "Puedes tomar una preimagen de `{U}` gracias
      a `{hU}`, con `choose`."
      choose V hV1 hV2 using hU
      Hint (hidden := true) "Puedes usar `{hV2}` para reescribir el objetivo."
      rw [← hV2]
      Hint (hidden := true) "Puefes aplicar `{hf1}`."
      apply hf1
      exact hV1
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint "Como `{f} '' {S}` es la imagen por una aplicación de un conjunto
      finito, tiene que ser finito. El teorema que nos dice esto es `Finite.image`,
      así que podemos aplicarlo."
      apply Finite.image
      exact hS2
    · Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
      intro x hx
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
      aplicando `{hS3}` a `{hx}`."
      have hx2 := hS3 hx
      Hint (hidden := true) "Puedes elegir un elemento de `{S}` (con `choose`) gracias a `{hx2}`."
      choose U hUF hxU using hx2
      Hint (hidden := true) "El elemento que tienes que usar es precisamente
      la imagen de `{U}` por `{f}`.

      Teclea `use {f} {U}`."
      use f U
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · use U
      · Hint (hidden := true) "Puedes aplicar `{hf2}`."
        apply hf2
        exact hUF
        exact hxU

end topo
