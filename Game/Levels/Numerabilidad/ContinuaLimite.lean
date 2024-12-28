import Game.Levels.Numerabilidad.ClausuraSucesion

World "Limites"
Level 11
Title "Continuidad en función de límites."

Introduction "
Si `X` es un espacio topológico primero numerable,
entonces una aplicación `f : X → Y` es contínua si
y solo si preserva límites
"





namespace topo
open topo espacio_topologico Set Function Nat


/--
Si `f : X → Y` es una aplicación entre un espacio `IAN` y
oytro espacio topológico, entonces `f` es contínua
si y solo si para toda sucesión `s` en `X`, las imágenes
de sus límites son límites de `f ∘ s`.
-/
TheoremDoc topo.caracterizacion_continua_limites as "caracterizacion_continua_limites" in "Limites"

Statement caracterizacion_continua_limites
  {X Y : Type} [espacio_topologico X] [espacio_topologico Y]
  (hX : IAN X) (f : X → Y) :
    continua f ↔ ∀ s : ℕ → X, ∀ x, limite s x → limite (f ∘ s) (f x) := by
  Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes introducir antecedentes y objetos arbitrarios con `intro`."
    intro h s x hs
    Hint (hidden := true) "Puedes aplicar un teorema ya visto."
    apply limite_continua
    exact h
    exact hs
  · Hint (hidden := true) "Puedes introducir antecedentes y objetos arbitrarios con `intro`."
    intro h
    Hint (hidden := true) "Será útil reescribir la continuidad en términos de cerrados."
    rw [continua_sii_cerrados]
    Hint (hidden := true) "Puedes introducir antecedentes y objetos arbitrarios con `intro`."
    intro C hC
    Hint (hidden := true) "Será útil reescribir el ser cerrado en términos de clausuras."
    rw [caracterizacion_cerrado_clausura] at hC ⊢
    Hint (hidden := true) "Para ver la igualdad entre conjuntos, se suele aplicar el
    principio de extensionalidad (`ext`)."
    ext x
    Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes introducir antecedentes y objetos arbitrarios con `intro`."
      intro hx
      Hint (hidden := true) "Recuerda que acabamos de ver un resultado
      que permite reescribir `{hx}` en términos de sucesiones (gracias a
      que tenemos la hipótesis `{hX}`)"
      rw [clausura_sucesion hX] at hx
      Hint (hidden := true) "Gracias a `{hx}` sabemos que existen
      ciertas sucesiones. Elige una con `choose`."
      choose s hs1 hs2 using hx
      Hint (hidden := true) "Usa `{hC}` para reescribir el objetivo."
      rw [← hC]
      Hint (hidden := true) "Será útil simplificar el objetivo y `{hs1}`."
      simp only [mem_preimage] at hs1 ⊢
      Branch
        rw [caracterizacion_clausura]
        Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
        intro U hU hfxU
        Hint (hidden := true) "Obten una nueva hipótesis (con `have`)
        aplicando `{h}` a `{s}`, `{x}`, y `{hs2}`."
        have h4 := h s x hs2
        Hint (hidden := true) "Obten una nueva hipótesis (con `have`)
        aplicando `{h4}` a `{U}`, `{hU}` y `{hfxU}`."
        have h3 := h4 U hU hfxU
        Hint (hidden := true) "Gracias a `{h3}` puedes elegir un número."
        choose n hn using h3
        Hint (hidden := true) "¿Qué elemento de `{Y}` puedes usar?"
        use f (s n)
        Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
        fconstructor
        · Hint (hidden := true) "Puedes aplicar `{hn}`."
          apply hn
          Hint (hidden := true) "Esto se cumple trivialmente."
          trivial
        · apply hs1
      apply aglomeracion_clausura hs1
      Hint (hidden := true) "Obten una nueva hipótesis (con `have`)
        aplicando `{h}` a `{s}`, `{x}`, y `{hs2}`"
      have h3 := h s x hs2
      Hint (hidden := true) "Puedes introducir antecedentes y objetos arbitrarios con `intro`."
      intro U hU hfxU n0
      Hint (hidden := true) "Obten una nueva hipótesis (con `have`)
        aplicando `{h3}` a `{U}`, `{hU}` y `{hfxU}`."
      have h4 := h3 U hU hfxU
      Hint (hidden := true) "Gracias a `{h4}` puedes elegir un número."
      choose n hn using h4
      Hint (hidden := true) "Observa que necesitas un número
      mayor o igual que `{n}` y que `{n0}`. ¿Cual puedes elegir?"
      use n + n0
      Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Esto es simple aritmética entera."
        omega
      · Hint (hidden := true) "Tienes una hipótesis que implica el objetivo."
        apply hn
        omega
    · Hint (hidden := true) "Puedes aplicar el resultado que dice
      que la clausura de un conjunto contiene al conjunto."
      apply clausura_contiene

end topo
