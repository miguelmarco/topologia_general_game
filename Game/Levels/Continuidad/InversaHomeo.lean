import Game.Levels.Continuidad.IdentidadHomeo

World "Continuidad"
Level 8
Title "Inversa de un homeomorfismo."

Introduction "La inversa de un homeomorfismo es un homeomorfismo.
"

namespace topo
open topo espacio_topologico Set Function

variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

theorem inversa_unica {A B : Type} (f : A → B) (g1 g2 : B → A)
  (hfg1 : f ∘ g2 = id) (hfg2 : g1 ∘ f = id) :
    g1 = g2 := by
  have h1 : g1 = g1 ∘ id := rfl
  have h2 : g2 = id ∘ g2 := rfl
  rw [h1]
  rw [h2]
  rw [← hfg1]
  rw [← hfg2]
  ext x
  simp only [comp_apply]

/--
Si tenemos aplicaciones `f : X → Y` y `g₁ g₂ : Y → X` tales que
`f ∘ g₂ = id` y `g₁ ∘ f = id` entonces `g₁ = g₁`
-/
TheoremDoc topo.inversa_unica as "inversa_unica" in "Utilidades"

NewTheorem topo.inversa_unica


/--
Si `f: X → Y` es un homeomorfismo y `g : Y → X` es inversa de `f`, entonces
`g` es un homeomorfismo.
-/
TheoremDoc topo.homeomorfismo_inversa as "homeomorfismo_inversa" in "Continuidad"

Statement homeomorfismo_inversa  (hf : homeomorfismo f) (h : Y → X) (hfh : h ∘ f = id)
    : homeomorfismo h := by
  Hint (hidden := true) "Debemos empezar reescribiendo la definición
  de homeomorfismo tanto en el objetivo como en `{hf}`."
  rw [def_homeomorfismo] at hf ⊢
  Hint (hidden := true) "Puedes separar las distintas partes de `{hf}`
  con `cases'` o `choose`."
  cases' hf with hhcont hf2
  Hint (hidden := true) "Ahora puedes elegir la aplicación que `{hf2}`
  te garantiza que existe (y sus propiedades) con `choose`."
  choose g hgcont hfin hgin using hf2
  Hint (hidden := true) "Ahora en realidad nos basta ver que `h = g`.
  Añade esta igualdad como un objetivo intermedio con `have haux : h = g`."
  have haux : h = g
  · Hint "Para demostrar esta igualdad, podemos usar un teorema que
    nos dice que si una aplicación (en este caso `{f}`) tiene inversa,
    la inversa es única, llamado `inversa_unica`.

    Para usarlo, símplemente teclea `apply inversa_unica {f}` y
    Lean pasará a pedirte que demuestres las condiciones que ese teorema
    establece."
    apply inversa_unica f
    Hint (hidden := true) "Esto es exactamente una de tus hipótesis."
    exact hgin
    Hint (hidden := true) "Y esto también es una hipótesis."
    exact hfh
  Hint (hidden := true) "Ahora podemos usar `{haux}` para reescribir el
  objetivo."
  rw [haux]
  Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Este objetivo es exactamente una de tus hipótesis."
    exact hgcont
  · Hint (hidden := true) "Fíjate que ahora debes probar que existe
    una inversa contonua de `{g}`. ¿Cual puedes usar?"
    use f

end topo
