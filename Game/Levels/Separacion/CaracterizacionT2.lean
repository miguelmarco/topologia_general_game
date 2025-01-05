import Game.Levels.Separacion.T2

World "Separacion"
Level 4
Title "Caracterización de espacios T₂"

Introduction "Veamos una caracterización de los espacios T₂."

namespace topo
open topo espacio_topologico

/--
Un espacio topológico es `T2` si y solo si los conjuntos
unipuntuales son la intersección de sus entornos cerrados.
-/
TheoremDoc topo.caracterizacion_T2 as "caracterizacion_T2" in "Separación"

Statement caracterizacion_T2 (X : Type) [espacio_topologico X] : T2 X ↔ ∀ (x : X), {x} = ⋂₀ {N ∈ cerrados | entorno x N } := by
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h x
    Hint (hidden := true) "La igualdad de conjuntos suele demostrarse por
    extensionalidad (`ext`)."
    ext y
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Introduce el antecedente con `intro`."
      intro hy
      Hint (hidden := true) "Puedes simplificar `{hy}`."
      simp only [Set.mem_singleton_iff] at hy
      Hint (hidden := true) "Usa `{hy}` para reescribir el objetivo."
      rw [hy]
      Hint (hidden := true) "Para ver que `{x}` está en la intersección de una familia,
      toma un conjunto arbitrario de la familia (con `intro`) y demuestra que está en él."
      intro N hN
      Hint (hidden := true) "Puedes separar `{hN}` en varias hipótesis con `choose`
      o `cases'`."
      choose hNC hNe using hN
      Hint (hidden := true) "Puedes aplicar el resultado que dice que los entrornos
      de un punto contienen al punto."
      apply entornos_N2
      exact hNe
    · Hint (hidden := true) "Introduce el antecedente con `intro`."
      intro hy
      Hint (hidden := true) "Puede ser útil reescribir la definición de espacio T₂."
      rw [def_T2] at h
      Hint (hidden := true) "Para poder usar `{h}`, necesitamos dos puntos
      distintos, así que parece que esta demostración habrá que hacerla por
      contradicción: supón que el objetivo es falso (con `by_contra`), y pasaremos
      a intentar demostrar una contradicción."
      by_contra hneg
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`) aplicando
      `{h}` a `{y}`, `{x}` y `{hneg}`."
      have h3 := h y x hneg
      Hint (hidden := true) "Puedes usar `{h3}` para elegir dos abiertos con sus propiedades
      (con  `choose`)."
      choose U V hU hV hUV hyU hxV using h3
      Hint (hidden := true) "Ahora podemos particularizar `{hy}` a un entorno cerrado
      concreto de `{x}` para obtener una nueva hipótesis (con `have`).

      ¿Cual puede ser el entorno cerrado que necesitamos?"
      have hyVc := hy Uᶜ
      Hint (hidden := true) "Ahora podemos aplicar `{hyVc}` (que nos dará
      una contradicción si `{U}ᶜ` está en la familia y `{y} ∈ {V}`.)"
      apply hyVc
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Habrá que reescribir la definición de cerrado."
        rw [def_cerrado]
        Hint (hidden := true) "Se puede simplificar esa expresión."
        simp only [compl_involutive, Function.Involutive.comp_self, cancela_inver]
        exact hU
      · Hint (hidden := true) "Puedes reescribir la definición de entorno."
        rw [def_entorno]
        Hint (hidden := true) "¿Qué abierto intermedio puedes usar?"
        use V
        Hint (hidden := true) "Separa el objetivo con `fconstructor`."
        fconstructor
        · exact hV
        Hint (hidden := true) "Separa el objetivo con `fconstructor`."
        fconstructor
        · exact hxV
        · Hint (hidden := true) "Toma un punto arbitrario de `{V}` con `intro`."
          intro z hzV hzU
          Hint (hidden := true) "Ahora puedes crear un nuevo objetivo (con `have`)
          para demostrar que `{z} ∈ {U} ∩ {V}`."
          have hz : z ∈ U ∩ V
          · trivial
          Hint (hidden := true) "Aprovecha `{hUV}` para reescribir `{hz}`."
          rw [hUV] at hz
          Hint (hidden := true) "`{hz}` es exactamente la contradicción que buscábamos."
          exact hz
      · exact hyU
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puede ser útil reesctibir la definición de espacio T₂."
    rw [def_T2]
    Hint (hidden := true) "Toma dos puntos distintos arbitrarios con `intro`."
    intro x y hxy
    Hint (hidden := true) "Necesitamos ver que `{x}` no está en la intersección
    de la familia de los entornos cerrados de `{y}`.
    Para ello, crea un nuevo objetivo con `have` y pasaremos a demostrarlo."
    have hx : x ∉ ⋂₀ { N ∈ cerrados | entorno y N}
    · Hint (hidden := true) "Puedes usar `{h}` para reescribir el objetivo (al revés)."
      rw [← h]
      Hint (hidden := true) "`{hxy}` dice exactamente eso."
      exact hxy
    Hint (hidden := true) "Observa que `{hx}` puede simplificarse para decir que hay un
    entorno cerrado de `{y}` al que `{x}` no pertenece."
    simp only [Set.mem_sInter, Set.mem_setOf_eq, and_imp, not_forall, exists_prop,
      exists_and_left] at hx
    Hint (hidden := true) "Gracias a `{hx}` puedes elegir un entorno cerrado de `{y}`
    que no contiene a `{x}` (con `choose`)."
    choose C1 hC1 hC1y hxC1 using hx
    Hint (hidden := true) "Puede ser útil reescribir la definición de entorno en `{hC1y}`."
    rw [def_entorno] at hC1y
    Hint (hidden := true) "Puedes usar `{hC1y}` para elegir un abierto (con sus correspondientes
    propiedades) con `choose`."
    choose V hV hyV hVC1 using hC1y
    Hint (hidden := true) "¿Qué abierto que contenga a `{x}` puedes usar?"
    use C1ᶜ
    Hint (hidden := true) "¿Qué abierto que contenga a `{y}` puedes usar?"
    use V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hC1
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hV
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Para ver la igualdad de dos conjuntos, usa `ext`
      para elegir un punto arbitrario, y demostraremos que está en un conjunto
      si y solo si está en el otro."
      ext z
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Introduce el antecedente con `intro`."
        intro hz
        Hint (hidden := true) "Puedes separar `{hz}` en dos hipótesis con `choose`
        o `cases'`."
        choose hz1 hz2 using hz
        Hint (hidden := true) "`{hz1}` nos dice que `{z}` no está en `{C1}ᶜ`,
        así que podemos aplicarlo para dar una contradicción."
        apply hz1
        Hint (hidden := true) "Puedes aplicar `{hVC1}`."
        apply hVC1
        exact hz2
      · simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_compl_iff,
        IsEmpty.forall_iff]
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hxC1
    · exact hyV


end topo
