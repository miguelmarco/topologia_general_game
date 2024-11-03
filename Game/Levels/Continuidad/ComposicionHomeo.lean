import Game.Levels.Continuidad.InversaHomeo
open espacio_topologico Set Function


World "Continuidad"
Level 9
Title "Composición de homeomorfismos."

Introduction "La composición de homeomorfismos es un homeomorfismo.
"

variable {X Y Z: Type} [espacio_topologico X] [espacio_topologico Y] [espacio_topologico Z] (f : X → Y)


/--
Si `f: X → Y` y `g : Y → Z` son homeomorfismos, entonces `g ∘ f` es un
homeomorfismo.
-/
TheoremDoc homeomorfismo_composicion as "homeomorfismo_composicion" in "Continuidad"

Statement homeomorfismo_composicion (g : Y → Z) (hf : homeomorfismo f) (hg : homeomorfismo g)
    : homeomorfismo (g ∘ f) := by
  Hint (hidden := true) "Hasta ahora hemos reescrito todas las definiciones
  que nos hemos encontrado, en este caso vamos a ver que nos podemos
  ahorrar algunos de esos pasos. Como `{hf}` dice que `{f}` es continua
  y que hay una inversa con unas propiedades, podemos desplegar todas
  esas hipótesis con `choose` directamente."
  choose fcont fi hficont hfif hffi using hf
  Hint (hidden := true) "También podemos extraer las hipótesis que
  forman `{hg}` con `choose`."
  choose gcont gi hgicont hgig hggi using hg
  Hint (hidden := true) "Y ahora podemos separar las distintas
  partes que internamente forman el objetivo, con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes aplicar un teorema que ya vimos, que dice
    que la composición de aplicaciones continuas es continua."
    apply composicion_continuas
    exact fcont
    exact gcont
  · Hint (hidden := true) "Para ver que existe una inversa de `{g} ∘ {f}`
    tenemos que darla. ¿Qué función debes usar?"
    use fi ∘ gi
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes volver a aplicar el teorema que asegura que la
      composición de aplicaciones continuas es continua."
      apply composicion_continuas
      exact hgicont
      exact hficont
    Hint (hidden := true) "Volvemos a tener que separar el objetivo en varios
    con `fconstructor`."
    fconstructor
    · Hint "Aquí vamos a necesitar poner el objetivo de una forma concreta,
      y para ello necesitamos un resultado auxiliar.

      Teclea `have haux : ({fi} ∘ {gi}) ∘ {g} ∘ {f} = {fi} ∘ ({gi} ∘ {g}) ∘ {f}`"
      have haux : (fi ∘ gi) ∘ g ∘ f = fi ∘ (gi ∘ g) ∘ f
      · Hint (hidden := true) "Esto es cierto por definición, así que se
        prueba con `rfl`."
        rfl
      Hint (hidden := true) "Ahora podemos usar `{haux}` para reescribir
      el objetivo como nos conviene."
      rw [haux]
      Hint (hidden := true) "Ahora puedes usar `{hgig}` para reescribir el objetivo."
      rw [hgig]
      Hint (hidden := true) "Prueba a simplificar."
      simp only [id_comp]
      exact hfif
    · Hint (hidden := true) "Igual que antes, necesitamos poner el objetivo
      de una forma concreta:

      `have haux : ({g} ∘ {f}) ∘ {fi} ∘ {gi} = {g} ∘ ({f} ∘ {fi}) ∘ {gi}`
      "
      have haux :  (g ∘ f) ∘ fi ∘ gi = g ∘ (f ∘ fi) ∘ gi
      · Hint (hidden := true) "También es cierto por definición. Se prueba
        con `rfl`."
        rfl
      Hint (hidden := true) "Puedes usar `{haux}` para reescribir."
      rw [haux]
      Hint (hidden := true) "Puedes usar `{hffi}` para reescribir."
      rw [hffi]
      Hint (hidden := true) "Simplifica."
      simp only [id_comp]
      exact hggi
