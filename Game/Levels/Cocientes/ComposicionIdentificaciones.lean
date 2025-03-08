import Game.Levels.Cocientes.Identificacion

World "Cocientes"
Level 10
Title "Composición de identificaciones."

Introduction "
En el anterior nivel vimos que la proyección a un cociente es una identificación.
Este hecho es, de hecho, una caracterización, ya que dada una identificación
`f : X → Y`, define una relación de equivalencia `∼f` , (llamada *inducida* por `f`)
dada por `x ≈ y ↔ f x = f y`. El teorema `def_inducida` dice como se define
esta relación.
En esta situación, `Y` es de hecho homeomorfo a `X /' ~f`.

El teorema `identificación cociente` (que aquí daremos por ya demostrado)
dice exactamente esto. Como consecuencia, las identificaciones son esencialmente
el mismo concepto que los cocientes.

En este nivel, veremos una propiedad de las identificaciones: la composición
de dos identificaciones es una identificación. Por lo tanto, el cociente de un
cociente es de hecho un cociente.
"




namespace topo
open topo espacio_topologico Set Function

variable {X: Type} [espacio_topologico X]

variable {Y : Type} [espacio_topologico Y]


instance equiv_inducida (f : X →  Y): Equiv X where
  r := by
    intro x y
    exact f x = f y
  iseqv := by
    fconstructor
    · simp only [implies_true]
    · intro x y hxy
      rw [hxy]
    · intro x y z hxy hyz
      rw [hxy,hyz]


notation3 "∼" f => equiv_inducida f

theorem def_equiv_inducida  (f : X → Y) :  ∀ (x₁ x₂ : X), (@Quotient.mk  X (equiv_inducida f)) x₁ = (@Quotient.mk X (equiv_inducida f) ) x₂ ↔ f x₁ = f x₂ := by
  intro x₁ x₂
  simp only [def_π, Quotient.eq]
  rfl

/--
Dada una aplicación `f : X → Y`,
el teorema `def_equiv_inducida x₁ x₂` nos dice que, para la relación de equivalencia
`∼f`,  se tiene que `∀ x₁ x₂, ⟦x₁⟧ = ⟦x₂⟧ ↔ f x₁ = f x₂`.
-/
TheoremDoc topo.def_equiv_inducida as "def_equiv_inducida" in "lemas-definición"

theorem identificacion_cociente (f : X → Y) (hf : identificacion f) : ∃ (h :  (X /' ∼f) → Y), homeomorfismo h ∧ f = h ∘ (@π X (equiv_inducida f))  := by
  let R := ∼f
  choose hf1 hf2 using hf
  choose g hg using hf1
  have haux : ∀ (c : X /' ∼f) , ∃ x, ⟦x⟧  = c
  · apply existe_representante
  choose l hl using haux
  fconstructor
  · exact f ∘l
  fconstructor
  fconstructor
  · intro U hU
    rw [def_abierto_cociente]
    rw [hf2] at hU
    have haux : {x | ⟦x⟧ ∈ f ∘ l ⁻¹' U} = f ⁻¹' U
    · ext t
      simp only [mem_preimage, comp_apply, mem_setOf_eq]
      have h2 : f (l ⟦t⟧) = f t
      · change l ⟦t⟧ ≈ t
        rw [← def_clase_equiv]
        rw [hl]
      rw [h2]
    rw [haux]
    exact hU
  fconstructor
  · exact π ∘  g
  fconstructor
  · intro U hU
    rw [def_abierto_cociente] at hU
    rw [hf2]
    have haux : {x | ⟦x⟧ ∈ U} = f ⁻¹' (π ∘ g ⁻¹' U)
    · ext t
      simp [hg,def_π ]
      have haux2 : ⟦t⟧ = ⟦g ( f t)⟧
      · rw [def_equiv_inducida f]
        rw [hg]
      rw [haux2]
    rw [haux] at hU
    exact hU
  fconstructor
  · ext t
    simp only [comp_apply, id_eq]
    rw [← hl t,def_π ,def_clase_equiv]
    change  f (g (f (l ⟦l t⟧))) = f ( l t)
    rw [hg,hl]
  · ext t
    simp only [comp_apply, id_eq]
    rw [← hg t]
    change (l (π (g (f (g t))))) ≈ (g t)
    rw [hg]
    rw [← def_clase_equiv,hl]
    rfl
  · ext t
    simp only [def_π, comp_apply, Quotient.eq]
    change t ≈ l ⟦t⟧
    rw [← def_clase_equiv,hl]


/--
Dada una identificación `f : X → Y`, el teorema `identificación_cociente` nos dice
que existe una aplicación `h :  (X /' ∼f) → Y` que es un homeomorfismo, y que además,
`f` coincide con `h ∘ π`
-/
TheoremDoc topo.identificacion_cociente as "identificacion_cociente" in "Cocientes"

NewTheorem topo.identificacion_cociente

/--
La composición de identificaciones es una identificación.
-/
TheoremDoc topo.composicion_identificaciones as "composicion_identificaciones" in "Cocientes"

Statement composicion_identificaciones {Z : Type} [espacio_topologico Z] (f : X → Y) (g : Y → Z) (hf : identificacion f) (hg : identificacion g ):
    identificacion (g ∘ f) := by
  Hint (hidden := true) "Puedes separar `{hf}` y `{hg}` en dos afirmaciones
  con `choose` o `cases'`."
  choose hf1 hf2 using hf
  choose hg1 hg2 using hg
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Para ver que es suprayectiva, toma un elemento arbitrario
    de `{Z}` con `intro`, y veamos que tiene una preimagen."
    intro z
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hg1}` a `{z}`."
    have hz1 := hg1 z
    Hint (hidden := true) "Gracias a `{hz1}`, puedes elegir una preimagen en
    `{Y}` con `choose`."
    choose y hy using hz1
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`) aplicando
    `{hf1}` a `{y}`."
    have hy1 := hf1 y
    Hint (hidden := true) "Gracias a `{hy1}` puedes elegir una preimagen en `X`
    con `choose`."
    choose x hx using hy1
    Hint (hidden := true) "¿Qué elemento de `{X}` puedes usar?"
    use x
    Hint (hidden := true) "Reescrive el objetivo con `{hy}`."
    rw [← hy]
    Hint (hidden := true) "Reescrive el objetivo con `{hx}`."
    rw [← hx]
    Hint (hidden := true) "Ahora el objetivo es trivialmente cierto."
    trivial
  · Hint (hidden := true) "Toma un conjunto de `{Z}` arbitrario con `intro`."
    intro U
    Hint (hidden := true) "Ahora puedes reescribir el objetivo usando `{hg2}`."
    rw [hg2]
    Hint (hidden := true) "Ahora puedes reescribir el objetivo usando `{hf2}`."
    rw [hf2]
    Hint (hidden := true) "El objetivo es trivialmente cierto."
    trivial

end topo
