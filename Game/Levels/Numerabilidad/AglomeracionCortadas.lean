import Game.Levels.Numerabilidad.LimiteHausdorff

World "Limites"
Level 9
Title "La aglomeración como intersección de clausuras."

Introduction "
Los puntos de aglomeración de una sucesión `s` son las intersecciones
de las clausuras de las subsucesiones truncadas.
"

namespace topo
open topo espacio_topologico Set Function Nat
variable {X : Type}  [espacio_topologico X]


/--
Dada una sucesión `s`, `aglomeracion_truncadas s` dice que `aglomeracion s  = ⋂₀ { (clausura { s n |  n ≥ m }) | m : ℕ }`.
-/
TheoremDoc topo.aglomeracion_truncadas as "aglomeracion_truncadas" in "Limites"



Statement aglomeracion_truncadas (s : ℕ → X) : (aglomeracion s : Set X) = (⋂₀ { (clausura { s n |  n ≥ m }) | m : ℕ } : Set X):= by
  Hint (hidden := true) "La igualdad de conjuntos se suele demostrar
  con el principio de extensionalidad. Teclea `ext x`."
  ext x
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro hx
    Hint (hidden := true) "Puede ser útil reescribir la definición
    de aglomeración en `{hx}`."
    rw [def_aglomeracion] at hx
    Hint (hidden := true) "Como queremos ver que `{x}` está en la
    intersección de una familia, toma un conjunto arbitrario de la familia
    con `intro`."
    intro S hS
    Hint (hidden := true) "Si no entiendes bien lo que quiere
    decir `{hS}`, prueba a simplificarlo."
    simp only [ge_iff_le, mem_setOf_eq] at hS
    Hint (hidden := true) "`{hS}` asegura que existe un cierto número
    natural. Eligelo con `choose`."
    choose m hm using hS
    Hint (hidden := true) "Como `{hm}` te dice qué conjunto es `{S}`,
    puedes usarlo para reescribir el objetivo."
    rw [← hm]
    Hint (hidden := true) "Será útil replantear el objetivo con
    la caracterización de los puntos de la clausura."
    rw [caracterizacion_clausura]
    Hint (hidden := true) "Toma un abierto arbitrario (y sus propiedades)
    con `intro`."
    intro U hU hxU
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hx}` a `{U}`, `{hU}`,  `{hxU}`y `{m}`."
    have hx2 := hx U hU hxU m
    Hint (hidden := true) "Ahora gracias a `{hx2}` puedes elegir un
    `n0` y sus propiedades."
    choose n0 hnm hnU using hx2
    Hint (hidden := true) "¿Qué punto puedes usar?"
    use (s n0)
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · exact hnU
    · Hint (hidden := true) "Si no ves claro qué es lo que hay que demostrar,
      puedes simplificar el objetivo."
      simp only [mem_setOf_eq]
      Hint (hidden := true) "¿Qué número puedes usar?"
      use n0
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Será útil reescribir la definición de
    aglomeración."
    rw [def_aglomeracion]
    Hint (hidden := true) "Puedes tomar un abierto arbitrario
    con `intro`."
    intro U hU hxU
    Hint (hidden := true) "Puedes tomar un número arbitrario con
    `intro`."
    intro n0
    Hint (hidden := true) "Ahora tendremos que ver que `{x}` está
    en la clausura de `\{ ({s} n) |  n ≥ {n0} \\}`. Añade ese objetivo
    secundario con `have {x} ∈ clausura  \{ ({s} n) |  n ≥ {n0} \\}`."
    have haux : x ∈ clausura { (s n) |  n ≥ n0}
    · Hint (hidden := true) "Es un caso particular de `{h}`, así que puedes
      aplicarlo."
      apply h
      Hint (hidden := true) "¿Qué número puedes usar?"
      use n0
    Hint (hidden := true) "Puede ser útil reescribir `{haux}` en
    términos de la caracterización de la clausura."
    rw [caracterizacion_clausura] at haux
    Hint (hidden := true) "Puedes obtener una nueva hipótesis
    (con `have`) aplicando `{haux}` a `{U}` `{hU}` y `{hxU}`."
    have hcar := haux U hU hxU
    Hint (hidden := true) "`{hcar}` te asegura que existen ciertos
    puntos. Puedes elegir uno con `choose`."
    choose y hy1 hy2 using hcar
    Hint (hidden := true) "puedes usar `{hy2}` para elegir un
    número."
    choose n hn hyn using hy2
    Hint (hidden := true) "¿Qué número puedes usar?"
    use n
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · exact hn
    · Hint (hidden := true) "Aprovecha `{hyn}` para reescribir el
      objetivo."
      rw [hyn]
      exact hy1


end topo
