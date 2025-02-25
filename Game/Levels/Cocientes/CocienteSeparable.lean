import Game.Levels.Cocientes.PropiedadUniversal
World "Cocientes"
Level 6
Title "Cociente de espacios separables."

Introduction "
Vamos a ver que el cociente de un espacio separable es separable.

Será útil usar el teorema `imagen_contable` que asegura que la imagen de un
conjunto contable es contable.
"




namespace topo
open topo espacio_topologico Set

variable {X: Type} [espacio_topologico X] [R : Equiv X]

theorem imagen_contable {Y Z : Type} {f : Y → Z} {C : Set Y} (hC : contable C) : contable (f '' C) := by
  cases' hC with hC1 hC2
  · left
    rw [hC1]
    exact image_empty f
  · right
    choose s hs using hC2
    use f ∘ s
    rw [hs]
    ext t
    simp only [mem_image, mem_setOf_eq, exists_exists_eq_and, Function.comp_apply]

/--
La imagen de un conjunto contable por una aplicación, es contable.
-/
TheoremDoc topo.imagen_contable as "imagen_contable" in "Utilidades"

NewTheorem topo.imagen_contable

/--
El cociente de un espacio separable es separable.
-/
TheoremDoc topo.cociente_separable as "cociente_separable" in "Cocientes"

Statement cociente_separable (h : separable X) : separable (X /' R) := by
  Hint (hidden := true) "Como `{h}` afirma que existe al menos un
  conjunto denso y contable en `{X}`, puedes elegirlo con `choose`."
  choose D hDden hDcont using h
  Hint (hidden := true) "Pare ver que el cociente es separable,
  tenemos que dar un conjunto que sea denso y contable.
  ¿Cual puedes usar?"
  use π '' D
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Será útil reescribir el objetivo y `{hDden}`
    usando la caracterización de denso."
    rw [caracterizacion_denso] at hDden ⊢
    Hint (hidden := true) "Puedes tomar un abierto arbitrario, y la hipótesis
    con `intro`."
    intro U hU hx
    Hint (hidden := true) "Gracias a `{hx}`, podemos elegir un elemento de `{U}`."
    choose x hx using hx
    Hint (hidden := true) "Necesitaremos ver que `{U}` es un abierto. Crea
    un objetivo secundario para ello con `have`."
    have haux : π ⁻¹' U  ∈ abiertos
    · Hint (hidden := true) "Basta aplicar que la aplicación cociente es contínua."
      apply cociente_continua
      exact hU
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hDden}` a `(π ⁻¹' {U})` y `{haux}`."
    have h2 := hDden (π ⁻¹' U) haux
    Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando
    (con `have`) que existe un representante de `{x}`."
    have haux2 := existe_representante x
    Hint (hidden := true) "Gracias a `{haux2}`, podemos elegir un representante
    de `{x}`."
    choose y hy using haux2
    Hint (hidden := true) "Para poder usar luego `{h2}`, necesitamos ver
    que existe un elemento de `π ⁻¹' {U}`, crea un objetivo secundario para
    demostrarlo con `have`."
    have haux2 : ∃ y, y ∈ π ⁻¹' U
    · Hint (hidden := true) "¿Qué elemento puedes usar?"
      use y
      Hint (hidden := true) "Será útil usar `{hy}` para reescribir `{hx}`."
      rw [← hy] at hx
      Hint (hidden := true) "Observa que el objetivo dice lo mismo que `{hy}`.g"
      exact hx
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{h2}` a `{haux2}`."
    have h3 := h2 haux2
    Hint (hidden := true) "Ahora gracias a `{h3}` puedes elegir un elemento de
    esa intersección."
    choose z hz1 hz2 using h3
    Hint (hidden := true) "¿Qué elemento puedes usar para demostrar el objetivo?"
    use ⟦z⟧
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Observa que `{hz1}` dice exactamente lo mismo que
      el objetivo."
      exact hz1
    · Hint (hidden := true) "Para ver que algo está en la imagen de `{D}`,
      hay que dar un elemento de `{D}` cuya imagen sea la clase buscada.
      ¿Cual puedes usar?"
      use z
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · exact hz2
      · Hint (hidden := true) "Esto es cierto por definición."
        rfl
  · Hint (hidden := true) "Puedes aplicar el teorema que dice que la imagen
    de un conjunto contable es contable."
    apply imagen_contable
    exact hDcont

end topo
