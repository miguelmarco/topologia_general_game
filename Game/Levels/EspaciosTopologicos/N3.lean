import Game.Levels.EspaciosTopologicos.N2
open Set espacio_topologico

World "EspaciosTopologicos"
Level 10
Title "Propiedades de entornos 3"


/--
Las familias de los entornos de cada punto en un espacio topológico cumplen `N3`.
-/
TheoremDoc entornos_N3 as "entornos_N3" in "Espacios Topológicos"

Statement entornos_N3 (X : Type) [espacio_topologico X] :∀ (x : X), ∀ N1  N2, entorno x N1 → entorno x N2 →  entorno x (N1 ∩ N2):= by
  Hint (hidden := true) "Como de costumbre, habrá que introducir los
  elementos arbitrarios y sus hipótesis con `intro`."
  intro x N1 N2 hN1 hN2
  Hint (hidden := true) "Como `{hN1}` y `{hN2}` nos dicen que
  existen conjuntos con ciertas propiedades, podemos elegir unos concretos
  usando `choose`."
  choose U1 hU1ab hxU1 hU1N1 using hN1
  choose U2 hU2ab hxU2 hU2N2 using hN2
  unfold entorno
  Hint (hidden := true) "¿Qué conjunto puedes usar como abierto
  intermedio?"
  use (U1 ∩ U2)
  Hint (hidden := true) "Recuerda que un objetivo construido con varias partes
  se puede descomponer con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes aplicar un axioma que afirma que la intersección de dos abiertos
    es abierto."
    apply interseccion_abiertos
    exact hU1ab
    exact hU2ab
  fconstructor
  · Hint (hidden := true) "Recuerda que pertenecer a una intersección
    también se puede descomponer en dos afirmaciones."
    fconstructor
    exact hxU1
    exact hxU2
  · Hint (hidden := true) "La forma habitual de demostrar que un conjunto
    está contenido en otro es tomar un elemento arbitrario del primero
    con `intro`."
    intro y hy
    Hint (hidden := true) "Ahora `{hy}` se puede descomponer
    en dos hipótesis con `cases'` o `choose`."
    choose hy1 hy2 using hy
    fconstructor
    · Hint (hidden := true) "Puedes aplicar `{hU1N1}`."
      apply hU1N1
      exact hy1
    · apply hU2N2
      exact hy2
