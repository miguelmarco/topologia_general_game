import Game.Levels.Bases.UnionBaseTotal

open espacio_topologico Set


World "Bases"
Level 3
Title "Intersección de dos elementos de una base."

Introduction "Veamos ahora otra propiedad de las bases.
"

variable {X : Type} [espacio_topologico X]

/--
Dado un punto en la intersección de dos elementos de una base, hay un tercer
elemento de la base intermedio entre el punto y la intersección.
-/
TheoremDoc interseccion_elementos_base as "interseccion_elementos_base" in "Espacios Topológicos"

Statement interseccion_elementos_base (B : Set (Set X)) (hB : base B) (B1 B2 : Set X)
    (hB1 : B1 ∈ B) (hB2 : B2 ∈ B) : ∀ x ∈ B1 ∩ B2, ∃ B3 ∈ B, x ∈ B3 ∧ B3 ⊆ B1 ∩ B2 := by
  Hint (hidden := true) "Como de costumbre, puedes introducir un elemento arbitrario."
  intro x hx
  Hint (hidden := true) "Puede ser útil usar la caracterización de las bases para reescribir `{hB}`."
  rw [caracterizacion_base] at hB
  Hint (hidden := true) "`{hB}` está formado por dos afirmaciones. Puedes obtenerlas por separado
  usando `choose`."
  choose hBab hBx using hB
  Branch
    apply hBx
    · apply interseccion_abiertos
      · apply hBab
        exact hB1
      · apply hBab
        exact hB2
    · exact hx
  Hint (hidden := true) "Fíjate en que `{hBx}` se puede aplicar a cualquier abierto, así que
  necesitarás demostrar que el conjunto que quieres usar es un abierto."
  Hint (hidden := true) "Puedes añadir la hipótesis de que `{B1} ∩ {B2}` es abierto con
  `have hB1B2ab : {B1} ∩ {B2} ∈ abiertos`; y luego pasar a demostrarla."
  have hB1B2ab : B1 ∩ B2 ∈ abiertos
  · Hint (hidden := true) "Recuerda que hay un axioma que afirma que la intersección de dos
    abiertos es abierto."
    apply interseccion_abiertos
    · apply hBab
      exact hB1
    · apply hBab
      exact hB2
  Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis aplicando `{hBx}` a `{B1} ∩ {B2}`(
  gracias a `{hB1B2ab}`) y `{x}` (gracias a `{hx}`)."
  have hx2 := hBx (B1 ∩ B2) hB1B2ab x hx
  exact hx2
