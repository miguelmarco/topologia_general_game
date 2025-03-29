import Game.Levels.Compacidad.CerradoCompacto

World "Compacidad"
Level 4
Title "Compactos en un espacio Hausdorff"

Introduction "Vamos a ver una especie de recíproco
del teorema anterior: en un espacio Hausdorff, los
compactos son cerrados.
"

namespace topo
open espacio_topologico topo Set Set.Finite

variable {X: Type} [Nonempty X] [espacio_topologico X]



/-

/--
En un espacio vacío, todos los conjuntos son compactos.
-/
TheoremDoc topo.espacio_vacio_compacto as "espacio_vacio_compacto" in "Compacidad"

theorem espacio_vacio_compacto {K : Set X} (h : ¬ Nonempty X) :
    compacto K := by
  simp only [not_nonempty_iff] at h
  rw [eq_empty_of_isEmpty K]
  intro F _ _
  use ∅
  simp only [empty_subset, finite_empty, recubrimiento, sUnion_empty, and_self]

/--
El conjunto vacio es compacto.
-/
TheoremDoc topo.vacio_compacto as "vacio_compacto" in "Compacidad"

theorem vacio_compacto : compacto (∅ : Set X) := by
  intro F _ _
  use ∅
  simp only [empty_subset, finite_empty, recubrimiento, sUnion_empty, and_self]

/--
La unión de dos compactos es compacta.
-/
TheoremDoc topo.union_compactos as "union_compactos" in "Compacidad"

theorem union_compactos {K1 K2 : Set X} (h1 : compacto K1) (h2 : compacto K2) :
    compacto (K1 ∪ K2) := by
  intro F hF hF2
  have hKF1 : recubrimiento K1 F
  · rw [def_recubrimiento] at hF2 ⊢
    tauto
  have hKF2 : recubrimiento K2 F
  · rw [def_recubrimiento] at hF2 ⊢
    rw [union_comm] at hF2
    tauto
  specialize h1 F hF hKF1
  specialize h2 F hF hKF2
  choose S1 hS1F hS1fin hS1K1 using h1
  choose S2 hS2F hS2fin hS2K2 using h2
  use S1 ∪ S2
  fconstructor
  · exact union_subset hS1F hS2F
  fconstructor
  · exact union hS1fin hS2fin
  rw [def_recubrimiento] at hS1K1 hS2K2 ⊢
  intro x hx
  cases' hx with hx hx
  · specialize hS1K1 hx
    choose U hU hxU using hS1K1
    use U
    fconstructor
    · left
      exact hU
    · exact hxU
  · specialize hS2K2 hx
    choose U hU hxU using hS2K2
    use U
    fconstructor
    · right
      exact hU
    · exact hxU

/--
Los conjuntos finitos son compactos
-/
TheoremDoc topo.finito_compacto as "finito_compacto" in "Compacidad"


theorem finito_compacto {K : Set X} (hK : Set.Finite K) : compacto K := by
  apply Finite.induction_on
  · exact hK
  · exact vacio_compacto
  · intro x U hx hU hUK
    rw [← union_singleton]
    apply union_compactos
    · exact hUK
    · intro F hFab hFx
      simp only [recubrimiento, singleton_subset_iff, mem_sUnion] at hFx
      choose U hUF hxU using hFx
      use {U}
      simp only [singleton_subset_iff, hUF, finite_singleton, recubrimiento, sUnion_singleton, hxU,
        and_self]
-/


/--
En un espacio Hausdorff, los compactos son cerrados.
-/
TheoremDoc topo.compacto_t2_cerrado as "compacto_t2_cerrado" in "Compacidad"

Statement compacto_t2_cerrado {K : Set X} (hX : T2 X) (hK : compacto K) :
    K ∈ cerrados := by
  Hint (hidden := true) "Será útil reescribir la definción de cerrado."
  rw [def_cerrado]
  Hint (hidden := true) "En este caso, lo más fácil será usar
  la caracterización de abierto en términos de ser entorno de sus puntos."
  rw [abierto_sii_entorno]
  Hint (hidden := true) "Toma un punto arbitrario con `intro`."
  intro x hx
  Hint (hidden := true) "Prueba a simplificar `{hx}`."
  simp only [mem_compl_iff] at hx
  Hint "Ahora es cuando vamos a usar que el espacio es T2,
  vamos a necesitar ver que para cada punto de `{K}`,
  hay abiertos que lo separan de `{x}`.

  Crea un nuevo objetivo con `have haux : ∀ y ∈ {K}, ∃ (U V : Set X), U ∈ abiertos ∧ V ∈ abiefrtos ∧ U ∩ V = ∅ ∧ {x} ∈ U ∧ {x} ∈ V`."
  have haux : ∀ y ∈ K, ∃ (U V : Set X), U ∈ abiertos ∧ V ∈ abiertos ∧ U ∩ V = ∅ ∧ x ∈ U ∧ y ∈ V
  · Hint (hidden := true) "Toma un punto arbitrario de `{K}` con `intro`."
    intro y hy
    Hint (hidden := true) "En realidad, basta aplicar que `{X}` es T2."
    apply hX
    Hint (hidden := true) "Supón que fueran iguales con `intro`."
    intro h
    Hint (hidden := true) "Para llegar a una contradicción,
    podemos aplicar `{hx}`."
    apply hx
    Hint (hidden := true) "Ahora solo hay que ver que `{x} ∈ {K}`,
    pero gracias a `{h}` podemos reescribirlo."
    rw [h]
    exact hy
  Hint "Ahora, gracias a `{haux}`, podemos tomar una función
  de elección, que nos de esa pareja de abiertos para cada punto.

  Usa `choose! g1 g2 hg1ab hg2ab hg1g2 hxg1 hxg2 using {haux}`."
  choose! g1 g2 hg1 hg2 hg3 hg4 hg5 using haux
  Hint (hidden := true) "`{g1}` y `{g2}` son funciones que nos
  proporcionan abiertos. Vamos a usar los abiertos dados por
  `{g2}` como recubrimiento de `{K}`. Para ello, vamos
  a introducir antes el objetivo secundario de que forman
  un recubrimiento de `{K}`.

  Escribe `have haux2 : recubrimiento {K} ({g2} '' {K})`."
  have haux : recubrimiento K (g2 '' K)
  · Hint (hidden := true) "Toma un punto de `{K}` con `intro`."
    intro y hy
    Hint (hidden := true) "Necesitamos dar un elemento de la imagen
    de `{g2}` que contenga a `{y}`. ¿Cual puedes usar?"
    use g2 y
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Hay que dar un elemento de `{K}`
      tal que su imagen sea `{g2} {y}`. ¿Cual puedes usar?"
      use y
    · Hint (hidden := true) "Puedes aplicar `{hg5}`."
      apply hg5
      exact hy
  Hint (hidden := true) "También necesitaremos ver que `{g2} '' {K}`
  está formado por abiertos. Para ello, crea un nuevo objetivo:

  `have haux2 : ({g2} '' {K}) ⊆ abiertos`."
  have haux2 : (g2 '' K)  ⊆ abiertos
  · Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Como `{U}` está en `{g2} '' {K}`,
    podemos elegir un elemento de `{K}` cuya imagen por `{g2}` sea `{U}`."
    choose y hy1 hy2 using hU
    Hint (hidden := true) "Reescribe el objetivo usando `{hy2}`."
    rw [← hy2]
    Hint (hidden := true) "Puedes aplicar `{hg2}`."
    apply hg2
    exact hy1
  Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis
  (con `have`) aplicando `{hK}` a `({g2} '' {K})`, `{haux2}` y `{haux}`. "
  have haux3 := hK (g2 '' K ) haux2 haux
  Hint (hidden := true) "Gracias a `{haux3}`, puedes elegir
  un subrecubrimiengo finito."
  choose S hS1 hS2 hS3 using haux3
  Hint "Ahora que ya tenemos un conjunto finito de abiertos,
  necesitaremos tomar sus correspondientes puntos (para a
  su vez, usarlos para elegir abiertos que contienen a `{x}`.)

  Teclea `have hS4 : ∀ U ∈ {S}, ∃ y, (y ∈ {K} ∧ ({g2} y) = U)`. "
  have hS4 : ∀ U ∈ S , ∃ y, (y ∈ K ∧  (g2 y) = U)
  · Hint (hidden := true) "Toma un elemento arbitrario de `{S}`
    con `intro`."
    intro U hU
    Hint (hidden := true) "Puedes aplicar `{hS1}`."
    apply hS1
    exact hU
  Hint "Ahora, gracias a `{hS4}`, podemos elegir una función
  que nos de un punto de `K` por cada abierto de `{S}`.

  Hazlo con `choose! f hf1 hf2 using {hS4}`."
  choose! f hf1 hf2  using hS4
  Hint "Recapitulando, ahora tenemos:

  - Un recubrimiento finito `{S}` de `{K}`
  - Una función `{f}`, que por cada elemento de `{S}` nos da un punto de `{K}`.
  - Una función `{g1}` que por cada punto de `{K}`, nos da un abierto que contienen a `{x}`.

  Juntando todo ello, podemos dar una familia finita de abiertos que contienen a `{x}`.
  Su intersección será el abierto que estamo buscando.

  ¿Puedes pensar cómo escribir exactamente el abierto que buscamos?
  "
  Hint (hidden := true) "Teclea `use ⋂₀ ({g1} '' ({f} '' {S}))`."
  use ⋂₀  (g1 '' (f '' S))
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Podemos aplicar que es una intersección finita."
    apply interseccion_finita_abiertos
    Hint (hidden := true) "Es la imagen por una aplicación de un conjunto
    finito, recuerda que hay un teorema que dice que eso es finito."
    apply Finite.image
    apply Finite.image
    exact hS2
    Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Usando `{hU}`, puedes elegir un
    elemento de `{f} '' {S}` cuya imagen por `{g1}` es `{U}`."
    choose L hL1 hL2 using hU
    Hint (hidden := true) "Reescribe el objetivo con `{hL2}`."
    rw [← hL2]
    Hint (hidden := true) "Puedes aplicar `{hg1}`."
    apply hg1
    Hint (hidden := true) "Gracias a `{hL1}`, puedes elegir una preimagen."
    choose R hR1 hR2 using hL1
    Hint (hidden := true) "Reescribe el objetivo con `{hR2}`."
    rw [← hR2 ]
    Hint (hidden := true) "Puedes aplicar `{hf1}`"
    apply hf1
    exact hR1
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Toma un elemento de la familia con `intro`."
    intro U hU
    Hint (hidden := true) "Gracias a `{hU}` puedes elegir un
    punto de `{f} '' {S}`."
    choose y hy hy2 using hU
    Hint (hidden := true) "Reescribe el objetivo con `{hy2}`."
    rw [← hy2]
    Hint (hidden := true) "Puedes aplicar `{hg4}`."
    apply hg4
    Hint (hidden := true) "Gracias a `{hy}`, puedes elegir
    un elemento de `{S}`."
    choose V hV1 hV2 using hy
    Hint (hidden := true) "Reescribe el objetivo con `{hV2}`."
    rw [← hV2]
    Hint (hidden := true) "Puedes aplicar `{hf1}`."
    apply hf1
    exact hV1
  · Hint (hidden := true) "Toma un punto arbitrario de `{K}`
    con `intro`."
    intro y hy hyK
    Hint (hidden := true) "Puedes obtener una nueva hipótesis
    (con `have`) aplicando `{hg5}` a `{y}` y `{hyK}`."
    have hy2 := hg5  y hyK
    Hint (hidden := true) "Puedes obtener una nueva hipótesis
    aplicando `{hS3}` a `{hyK}`."
    have hy3 := hS3 hyK
    Hint (hidden := true) "Gracias a `{hy3}` puedes elegir
    un abierto y sus propiedades."
    choose U hU1 hU2 using hy3
    Hint (hidden := true) "Ahora necesitaremos demostrar que
    `{y} ∈ {g1} ({f} {U})`. Crea un nuevo objetivo (con `have`)
    para demostrarlo."
    have hy5 : y ∈ g1 (f U)
    · Hint (hidden := true) "Puedes aplicar `{hy}`."
      apply hy
      Hint (hidden := true) "Hay que dar un elemento de
      `{f} '' {S}` cuya imagen sea `{f} {U}`. Hay uno
      que puedes usar de forma evidente."
      use f U
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "¿Qué elemento de `{S}` puedes usar?"
        use U
      · Hint (hidden := true) "Esto es cierto trivialmente."
        rfl
    Hint (hidden := true) "Ahora que ya hemos visto que
    `{y}` está en `{g1} ({f} {U})`, si podemos ver que además
    está en `{g2} ({f} {U})`, tendremos la contradiccion.

    Introduce un nuevo objetivo con `have`."
    have hy4 : y ∈ g2 (f U)
    · Hint (hidden := true) "Puedes reescribir el objetivo con `{hf2}`."
      rw [hf2]
      exact hU2
      exact hU1
    Hint (hidden := true) "Ahora ya puedes ver que
    `{y} ∈ {g1} ({f} {U}) ∩ {g2} ({f} {U})`.
    Crea ese objetivo con `have`."
    have hy6 : y ∈ g1 (f U) ∩ g2 (f U)
    · trivial
    Hint (hidden := true) "Puedes reescribir `{hy6}` con `{hg3}`."
    rw [hg3] at hy6
    Hint (hidden := true) "La contradicción es trivial ahora."
    trivial
    Hint (hidden := true) "Puedes aplicar `{hf1}`."
    apply hf1
    exact hU1


end topo
