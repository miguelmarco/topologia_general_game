import Game.Levels.Continuidad.ComposicionHomeo


World "Continuidad"
Level 10
Title "Caracterización de homeomorfismos."

Introduction "Una biyección es un homeomorfismo si y sólo es continua y abierta.
"
namespace topo
open topo espacio_topologico Set Function
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

def abierta := ∀ U ∈ abiertos, f '' U ∈ abiertos

/--
Una aplicación `f : X → Y` entre espacios métricos es *abierta* si la imagen
de todo abierto es abierto.
-/
DefinitionDoc abierta as "abierta"

NewDefinition abierta

/--
Una aplicación entre espacios topológicos que tenga inversa,
es un homeomorfismo si y solo si es continua y abierta.
-/
TheoremDoc topo.homeomorfismo_sii_continua_abierta as "homeomorfismo_sii_continua_abierta" in "Continuidad"

Statement homeomorfismo_sii_continua_abierta (fi : Y → X) (hffi : f ∘ fi = id) (hfif : fi ∘ f = id):
    homeomorfismo f ↔  continua f ∧ abierta f:= by
  Hint (hidden := true) "Separa en dos objetivos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes obtener varias hipótesis de `{h}` con `choose` o `cases'`."
    choose hfcont g hgcont hgf hfg using h
    Hint (hidden := true) "Separa en varios objetivos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
      intro U hU
      Hint (hidden := true) "Puedes aplicar que `{f}` es continua."
      apply hfcont
      exact hU
    · Hint (hidden := true) "Introduce un abierto arbitrario con `intro`."
      intro U hU
      Hint (hidden := true) "Ahora no tenemos ninguna hipótesis que nos diga que la imagen de un
      abierto es abierto. Así que necesitamos poner el objetivo como una preimagen.

      `have haux : {f} '' {U} = {g} ⁻¹ {U}`"
      have haux : f '' U = g ⁻¹' U
      · Hint (hidden := true) "Para ver la igualdad de dos conjuntos, hay que aplicar el principio
        de extensionalidad, con `ext`."
        ext y
        Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
        fconstructor
        · Hint (hidden := true) "Introduce el antecedente con `intro`."
          intro hy
          Hint (hidden := true) "Como `{hy}` nos asegura que existen preimágenes de `{y}`,
          puedes elegir una de ellas (y sus hipótesis) con `choose`."
          choose x hxU hxy using hy
          Hint (hidden := true) "Ahora puedes usar `{hxy}` para reescribir el objetivo (de derecha a izquierda)."
          rw [← hxy]
          Hint (hidden := true) "Puedes simplificar la expresión gracias a `{hgf}`."
          simp only [mem_preimage, hgf, cancela_inver]
          exact hxU
        · Hint (hidden := true) "Introduce el antecedente con `intro`."
          intro hy
          Hint (hidden := true) "Ahora hay que ver que `{y}` tiene una preimagen en `{U}`.
          ¿Se te ocurre cual puedes usar?"
          Hint (hidden := true) "`use {g} {y}`"
          use g y
          fconstructor
          · exact hy
          · Hint (hidden := true) "Puedes simplificar gracias a `{hfg}`."
            simp only [hfg, cancela_inver]
      Hint (hidden := true) "Ahora podemos usar `{haux}` para reescribir el objetivo."
      rw [haux]
      Hint (hidden := true) "Puedes aplicar la continuidad de `{g}`."
      apply hgcont
      exact hU
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes obtener dos hipótesis a pertir de `{h}` mediante `choose` o `cases'`."
    choose hfcont hfab using h
    Hint (hidden := true) "Separa en varios objetivos con `fconstructor`."
    fconstructor
    · exact hfcont
    · Hint (hidden := true) "Ahora hay que demostrar que existe una cierta `g` inversa de `f`. ¿Cual puedes usar?"
      use fi
      Hint (hidden := true) "Separa en varios objetivos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
        intro U hU
        Hint (hidden := true) "No sabemos nada sobre como trata `{fi}` a los abiertos,
        así que tendremos que expresar `{fi} ⁻¹' {U}` en términos de `{f}`. Para ello
        podemos usar `have` y enunciar una afirmación que tendremos que probar. ¿Qué
        afirmación crees que te será útil?"
        Hint (hidden := true) "`have haux : {fi} ⁻¹' {U} = {f} '' {U}`"
        have haux : fi ⁻¹' U = f '' U
        · Hint (hidden := true) "Para probar la igualdad entre dos conjuntos, toma un elemento
          arbitrario con `ext`."
          ext y
          Hint (hidden := true) "Separa en dos objetivos con `fconstructor`."
          fconstructor
          · Hint (hidden := true) "Introduce el antecedente con `intro`."
            intro hy
            Hint (hidden := true) "Tenemos que demostrar que hay alguna preimagen de `{y}`.
            ¿Cómo puedes encontrarla?"
            use fi y
            Hint (hidden := true) "Separa en dos objetivos con `fconstructor`."
            fconstructor
            · Hint (hidden := true) "Una de las hipótesis dice exactamente lo que pide el objetivo."
              exact hy
            · Hint (hidden := true) "Prueba a simplificar el objetivo con `{hffi}`."
              simp only [hffi, cancela_inver]
          · Hint (hidden := true) "Introduce el antecedente con `intro`."
            intro hy
            Hint (hidden := true) "`{hy}` te asegura que existe alguna preimagen de `{y}`;
            puedes elegir una (y sus hipótesis) con `choose`."
            choose x hxU hxy using hy
            Hint (hidden := true) "Puedes usar `{hxy}` para reescribir el objetivo (de derecha a izquierda)."
            rw [← hxy]
            Hint (hidden := true) "Prueba a simplificar el objetivo."
            simp only [mem_preimage, hfif, cancela_inver]
            exact hxU
        Hint (hidden := true) "Ahorda, gracias a `{haux}`, podemos reescribir el objetivo."
        rw [haux]
        Hint (hidden := true) "Observa que puedes aplicar una hipótesis que te dice que
        la imagen de un abierto es abierto."
        apply hfab
        exact hU
      fconstructor
      · exact hfif
      · exact hffi

end topo
