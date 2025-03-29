import Game.Levels.Compacidad.ImagenCompacto

World "Compacidad"
Level 3
Title "Cerrado en un compacto"

Introduction "Veamos que un cerrado dentro de un compacto,
es a su vez compacto.

En este nivel necesitaremos usar que un subconjunto de un
conjunto finito, es a su vez finito. El teorema
que nos dice esto se llama `Finite.subset`.
"

namespace topo
open espacio_topologico topo Set Set.Finite

variable {X: Type} [espacio_topologico X]

/--
Si tenemos un conjunto `F` y una hipótesis `hF : Set.Finite F` que dice que
es finito, `Finite.subset hF` dice que cualquier subconjunto de `F` es finito.
-/
TheoremDoc Set.Finite.subset as "Finite.subset" in "Utilidades"

/--
Un cerrado contenido en un compacto, es compacto.
-/
TheoremDoc topo.cerrado_compacto as "cerrado_compacto" in "Compacidad"

Statement cerrado_compacto (K C : Set X) (hK : compacto K) (hC : C ∈ cerrados) (hCK : C ⊆ K) :
    compacto C := by
  Hint (hidden := true) "Toma un recubrimiento abierto de `{C}` con `intro`."
  intro F hFab hFC
  Hint (hidden := true) "Para construir un recubrimiento abierto de `{K}` que podamos
  usar, tenemos que añadir el complementario de `{C}`.

  Teclea `let G := F ∪ \{Cᶜ}`."
  let G := F ∪ {Cᶜ}
  Hint (hidden := true) "Veamos que `{G}` está formado por abiertos:
  teclea `have hGab : {G} ⊆ abiertos`."
  have hGab : G ⊆ abiertos
  · Hint (hidden := true) "Toma un elemento de `{G}` con `intro`."
    intro U hU
    Hint (hidden := true) "Puedes simplificar la definición de `{G}`
    en `{hU}` con `simp [{G}] at `{hU}`."
    simp only [union_singleton, mem_insert_iff, G] at hU
    Hint (hidden := true) "Ahora vamos a tener que tratar por separado
    los dos posibles casos de `{hU}` (con `cases'`)."
    cases' hU with hU hU
    · Hint (hidden := true) "Puedes reescribir el objetivo con `{hU}`."
      rw [hU]
      Hint (hidden := true) "Observa que eso es justo lo que dice `{hC}`."
      exact hC
    · Hint (hidden := true) "Puedes aplicar `{hFab}`."
      apply hFab
      exact hU
  Hint (hidden := true) "Ahora tenemos que ver que `{G}` es un recubrimiento
  de `{K}`.

  Teclea `hGrec : recubrimiento {K} {G}`."
  have hGrec : recubrimiento K G
  · Hint (hidden := true) "Toma un punto de `{K}` con `intro`."
    intro x hx
    Hint (hidden := true) "Ahora tenemos que tratar dos posibles casos:
    que `{x} ∈ {C}`, o que no. Usa la táctica `by_cases`."
    by_cases hcas : x ∈ C
    · Hint (hidden := true) "En este caso, podemos obtener una hipótesis
      nueva (con `have`) aplicando `{hFC}` a `{hcas}`."
      have haux := hFC  hcas
      Hint (hidden := true) "Ahora, gracias a `{haux}`, podemos elegir un
      elemento de `{F}` que contiene a `{x}` (con `choose`)."
      choose U hUF hxU using haux
      Hint (hidden := true) "¿Qué elemento de `{G}` puedes usar?"
      use U
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Puedes simplificar el objetivo usando la
        definición de `{G}` con `simp [{G}]`."
        simp only [union_singleton, mem_insert_iff, G]
        Hint (hidden := true) "¿Cual de las dos opciones vas a poder demostrar?
        ¿La de la izquierda o la de la derecha?"
        right
        exact hUF
      · exact hxU
    · Hint (hidden := true) "En este caso, en el que `{x}` no está
      en `{C}`, ¿qué elemento de `{G}` puedes usar?"
      use Cᶜ
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Simplifica la definición de `{G}` con `simp [{G}]`."
        simp only [union_singleton, mem_insert_iff, true_or, G]
      · exact hcas
  Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis (con `have`)
  aplicando `{hK}` a `{G}`, `{hGab}` y `{hGrec}`."
  have haux := hK G hGab hGrec
  Hint (hidden := true) "Puedes elegir un subrecubrimiento finito de `{G}`
  gracias a `{haux}`."
  choose S hSG hSfin hSK using haux
  Hint (hidden := true) "Ahora debes usar un subrecubrimiento de `{F}`,
  observa que `{S}` puede contener a `{C}ᶜ`, así que no puedes usarlo."
  Hint (hidden := true) "Usa `{S} ∩ {F}`."
  use S ∩ F
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Basta simplificar el objetivo."
    simp only [inter_subset_right]
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Ahora podemos aplicar `Finite.subset {hSfin}`."
    apply Finite.subset hSfin
    Hint (hidden := true) "Esto se puede demostrar con el simplificador."
    simp only [inter_subset_left]
  · Hint (hidden := true) "Toma un elemento arbitrario de `{C}` con `intro`."
    intro x hx
    Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando `{hCK}`
    a `{hx}` (con `have`)."
    have hxK := hCK hx
    Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando `{hSK}`
    a `{hxK}`."
    have hxS := hSK hxK
    Hint (hidden := true) "Gracias a `{hxS}` puedes elegir un abierto de `{S}`
    que contiene a `{x}` (con `choose`)."
    choose U hUS hxU using hxS
    Hint (hidden := true) "¿Qué elemento de `{S} ∩ {F}` puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · exact hUS
      · Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando `{hSG}` a `{hUS}`."
        have hUG := hSG hUS
        Hint (hidden := true) "Puedes simplificar la definición de `{G}` en `{hUG}`."
        simp only [union_singleton, mem_insert_iff, G] at hUG
        Hint (hidden := true) "Ahora hay que tratar los dos posibles
        cases de `{hUG}`. Usa la táctica `cases'`."
        cases' hUG with hUG hUG
        · Hint (hidden := true) "Puedes usar `{hUG}` para reescribir `{hxU}`."
          rw [hUG] at hxU
          Hint (hidden := true) "Ahora tenemos dos afirmaciones contradictorias,
          así que este caso trivialmente no puede darse."
          trivial
        · exact hUG
    · exact hxU

end topo
