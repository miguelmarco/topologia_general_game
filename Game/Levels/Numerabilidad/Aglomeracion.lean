import Game.Levels.Numerabilidad.Limite

World "Limites"
Level 2
Title "Puntos de aglomeración y subsucesiones."

Introduction "
Los límites de una subsucesión, son puntos de aglomeración
de la sucesión.

"

namespace topo
open topo espacio_topologico Set Function Nat
variable {X : Type} [espacio_topologico X]


/--
Si `s'` es una subsucesión de `s`, entonces los límites de `s'` son
puntos de aglomeración de `s`.
-/
TheoremDoc topo.aglomeracion_subsucesion as "aglomeracion_subsucesion" in "Limites"

Statement aglomeracion_subsucesion (s1 s2 : ℕ → X) (h : subsucesion s1 s2) (x : X) :
    limite s2 x → aglomeracion s1 x := by
  Hint (hidden := true) "Puede ser útil reescribir la definición de subsucesión."
  rw [def_subsucesion] at h
  Hint (hidden := true) "Gracias a `{h}` podemos elegir una `f` y sus propiedades."
  choose f hf1  hf2 using h
  Hint (hidden := true) "Introduce el antecedente con `intro`."
  intro hx
  Hint (hidden := true) "Puedes reescribir la definición de límite en `{hx}`, y
  la de aglomeración en el objetivo."
  rw [def_limite] at hx
  rw [def_aglomeracion]
  Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
  intro U hU hxU
  Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
  aplicando `{hx}` a `{U}`, `{hU}` y `{hxU}`."
  have hx2 := hx U hU hxU
  Hint (hidden := true) "Puedes elegir un `n0` usando `{hx2}`."
  choose n0 hn0 using hx2
  Hint (hidden := true) "Toma un natural arbitrario con `intro`."
  intro n1
  Hint (hidden := true) "Puedes reescribir `{hf2}` en `{hn0}`."
  rw [hf2] at hn0
  Hint (hidden := true) "Y ahora simplificar en `{hn0}`."
  simp only [ge_iff_le, comp_apply] at hn0
  Hint (hidden := true) "Ahora, el natural que tendremos que usar dependerá de si
  `{n0} ≤ {n1}` o no. Separa el objetivo en dos casos con `by_cases hcas : `{n0} ≤ {n1}`."
  by_cases hcas : n0 ≤ n1
  · Hint (hidden := true) "En este caso, podemos usar directamente `{f} {n1}`."
    use f n1
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Esto es lo que dice `subsucesion_creciente`, así que
      puedes aplicarlo."
      apply subsucesion_creciente
      exact hf1
    · Hint (hidden := true) "Ahora podemos aplicar `{hn0}`."
      apply hn0
      Hint (hidden := true) "Esto es justo lo que hemos supuesto en `{hcas}`."
      exact hcas
  · Hint (hidden := true) "En este caso, el que hay que usar es `{f} {n0}`."
    use f n0
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Necesitaremos que `{f} {n0} ≥ {n0}`, así que
      tenemos que obtener una nueva hipótesis con `have haux := subsucesion_creciente {hf1} {n0}`."
      have haux := subsucesion_creciente hf1 n0
      Hint (hidden := true) "Y ahora el objetivo se demuestra por aritmética lineal."
      linarith
    · Hint (hidden := true) "Podemos aplicar `{hn0}`."
      apply hn0
      Hint (hidden := true) "Esto es trivialmente cierto."
      trivial

end topo
