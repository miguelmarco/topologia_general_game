import Game.Levels.Cocientes.CocienteSeparable
World "Cocientes"
Level 7
Title "Cociente de espacios primero numerables."

Introduction "
Vamos a ver que, si la proyección es abierta,
el cociente de un espacio primero numerable es primero numerable.
"




namespace topo
open topo espacio_topologico Set

variable {X: Type} [espacio_topologico X] [R : Equiv X]



@[app_unexpander Quotient.mk]
def unexpandQuotientmk :  Lean.PrettyPrinter.Unexpander
| `($(_)) => `(π)

/--
El cociente de un espacio IAN es IAN si la proyección es abierta.
-/
TheoremDoc topo.cociente_IAN as "cociente_IAN" in "Cocientes"

Statement cociente_IAN (h : IAN X) (hπ : abierta (π : X → X /' R )) : IAN (X /' R) := by
  Hint (hidden := true) "Toma un punto arbitrario con `intro`."
  intro c
  Hint (hidden := true) "Gracias al teorema que te dice que
  todo elemento de un cociente tiene un representante, puedes
  obtener una nueva hipótesis (con `have`) que diga que `{c}`
  tiene un representante."
  have hrepr := existe_representante c
  Hint (hidden := true) "Puedes usar `{hrepr}` para elegir
  un representante (con `choose`)."
  choose x hx using hrepr
  Hint (hidden := true) "Puedes obtener una nueva hipótesis
  (con `have`) aplicando `{h}` a `{x}`."
  have h2 := h x
  Hint (hidden := true) "Separa `{h2}` en dos hipótesis con
  `choose` o `cases'`."
  choose B hB1 hB2 using h2
  Hint (hidden := true) "¿Cual será la base de entornos de `{c}`
  que puedes usar?"
  Hint (hidden := true) "Prueba con `\{π '' U | U ∈ {B}}`."
  use {π '' U  |  U ∈ B}
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes usar `{hx}` para reescribir el objetivo."
    rw [← hx]
    Hint (hidden := true) "Puedes aplicar el teorema que asegura que
    la imagen por una aplicación continua y abierta de una base de entornos,
    es una base de entornos."
    apply imagen_base_entornos
    Hint (hidden := true) "Puedes aplicar el teorema que dice que
    la proyección al cociente es continua."
    apply cociente_continua
    Hint (hidden := true) "El objetivo es exactamente una hipótesis."
    apply hπ
    Hint (hidden := true) "El objetivo es exactamente una hipótesis."
    apply hB1
  · Hint (hidden := true) "Puedes aplicar el teorema que dice que la imagen
    de un conjunto contable es contable."
    apply imagen_contable
    exact hB2



end topo
