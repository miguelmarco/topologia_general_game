import Game.Levels.Cocientes.CocienteIAN
World "Cocientes"
Level 8
Title "Cociente de espacios T1."

Introduction "
Vamos a ver qué debe de cumplir la relación de equivalencia para que
el cociente sea T1.
"




namespace topo
open topo espacio_topologico Set

variable {X: Type} [espacio_topologico X] [R : Equiv X]


/--
El cociente de un espacio T1 es T1 si y solo si las clases de equivalencia
son cerradas.
-/
TheoremDoc topo.cociente_T1 as "cociente_T1" in "Cocientes"

Statement cociente_T1 : T1 (X /' R) ↔ ∀ x , {y | y ≈ x} ∈ (cerrados : Set (Set X)) := by
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Asume el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Toma un punto arbitrario con `intro`."
    intro x
    Hint (hidden := true) "Será útil reescribir el objetivo usando
    la definición de cerrado."
    rw [def_cerrado]
    Hint (hidden := true) "Reescribe el objetivo en términos de entornos."
    rw [abierto_sii_entorno]
    Hint (hidden := true) "Toma un punto arbitrario con `intro`."
    intro y hy
    Hint (hidden := true) "Puedes simplificar `{hy}`."
    simp only [mem_compl_iff, mem_setOf_eq] at hy
    Hint (hidden := true) "Puedes reescribir `{hy}` en tèrminos de igualdad
    de clases de equivalencia."
    rw [← def_clase_equiv] at hy
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{h}` a `⟦{y}⟧` , `⟦{x}⟧` y `{hy}`."
    have h2 := h ⟦y⟧ ⟦x⟧ hy
    Hint (hidden := true) "Gracias a `{h2}`, puedes elegir un abierto
    con ciertas propiedades."
    choose U hU hUx hUy using h2
    Hint (hidden := true) "Como `{U}` es un abierto en el cociente,
    puedes reescribir `{hU}` con la definición de los abiertos
    de un cociente."
    rw [def_abierto_cociente] at hU
    Hint (hidden := true) "Piensa qué abierto intermedio entre
    `{y}` y `\{y | y ≈ {x}}ᶜ` puedes usar."
    use {z | ⟦z⟧ ∈ U}
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hUx
    · Hint (hidden := true) "Para ver el contenido entre conjuntos,
      toma un elemento arbitrario del primer conjunto con `intro`,
      y demuestra que debe estar en el segundo."
      intro z hz
      Hint (hidden := true) "Observa que el objetivo es realmente una
      negación, así que puedes asumir aquello que se niega (con `intro`)
      y pasar a ver que hay una contradicción."
      intro hzn
      Hint (hidden := true) "Prueba a simplificar `{hzn}` y `{hz}`."
      simp only [mem_setOf_eq] at hzn
      simp only [mem_setOf_eq] at hz
      Hint (hidden := true) "Observa que `{hUy}` es a su vez una negación,
      así que podemos aplicarlo para que baste demostrar aquello que niega."
      apply hUy
      Hint (hidden := true) "Prueba a reescribir `{hzn}` en términos de
      clases de equivalencia."
      rw [← def_clase_equiv] at hzn
      Hint (hidden := true) "Ahora puedes usar `{hzn}` para reescribir `{hz}`."
      rw [hzn] at hz
      exact hz
  · Hint (hidden := true) "Asume el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Toma dos puntos distintos con `intro`."
    intro x y hxy
    Hint (hidden := true) "Obten una nueva hipótesis (con `have`)
    que diga que existe un representante de `{y}`."
    have hy := existe_representante y
    Hint (hidden := true) "Elige un representante de `{y}` con `choose`."
    choose y' hy' using hy
    Hint (hidden := true) "Obtén una nueva hipótesis (con `have`)
    aplicando `{h}` a `{y'}`."
    have h2 := h y'
    Hint (hidden := true) "Reescribe `{h2}` con la definición de cerrado."
    rw [def_cerrado] at h2
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    Branch
      use (univ \ {y})
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Reescribe el objetivo usando la definición
        de abierto en un cociente."
        rw [def_abierto_cociente]
        Hint (hidden := true) "Usa `{hy'}` para reescribir el objetivo."
        rw [← hy']
        Hint (hidden := true) "Prueba a simplificar el objetivo."
        simp only [mem_diff, mem_univ, mem_singleton_iff, Quotient.eq, true_and]
        Hint (hidden := true) "Observa que el objetivo dice exactamente lo mismo que `{h2}`."
        exact h2
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Prueba a simplificar el objetivo."
        simp only [mem_diff, mem_univ, mem_singleton_iff, true_and]
        exact hxy
      · Hint (hidden := true) "Prueba a simplificar el objetivo."
        simp only [mem_diff, mem_univ, mem_singleton_iff, not_true_eq_false, and_false,
        not_false_eq_true]
    use {y}ᶜ
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Reescribe el objetivo usando la definición
      de abierto en un cociente."
      rw [def_abierto_cociente]
      Hint (hidden := true) "Usa `{hy'}` para reescribir el objetivo."
      rw [← hy']
      Hint (hidden := true) "Prueba a simplificar el objetivo."
      simp only [mem_compl_iff, mem_singleton_iff, Quotient.eq]
      Hint (hidden := true) "Observa que el objetivo dice exactamente lo mismo que `{h2}`."
      exact h2
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Prueba a simplificar el objetivo."
      simp only [mem_compl_iff, mem_singleton_iff]
      exact hxy
    · Hint (hidden := true) "Prueba a simplificar el objetivo."
      simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, not_false_eq_true]

end topo
