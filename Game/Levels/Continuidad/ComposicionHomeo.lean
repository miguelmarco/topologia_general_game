import Game.Levels.Continuidad.InversaHomeo
open espacio_topologico Set Function


World "Continuidad"
Level 9
Title "Composición de homeomorfismos."

Introduction "La composición de homeomorfismos es un homeomorfismo.
"

@[simp]
theorem cancela_inver {X Y : Type} {f : X → Y} {g : Y → X} {x  : X} (h : g ∘ f = id) :
    g (f x) = x := by
  change (g ∘ f) x = x
  rw [h]
  rfl

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
    · Hint "Para demostrar la igualdad entre dos aplicaciones, podemos aplicar el *principio
      de extensionalodad*, que nos dice que dos aplicaciones son iguales si y solo si la
      imagen de cualquier elemento coincide. Para ello, podemos usar la táctica `ext`,
      que tomará un elemento cualquiera y tendremos que demostrar que ambas imágenes coinciden.

      Teclea `ext x`."
      ext x
      Hint (hidden := true) "Ahora podemos simplificar el objetivo con `simp`."
      simp only [comp_apply, id_eq]
      Hint (hidden := true) "Podemos seguir simplificando más si usamos `{hgig}`: teclea
      `simp [{hgig}]`"
      simp only [hgig, cancela_inver]
      Hint (hidden := true) "Y podemos seguir simplificando con `{hfif}`."
      simp only [hfif, cancela_inver]
    · Hint (hidden := true) "Igual que antes, aplicamos la extensionalidad a un elemento
      cualquiera con `ext y`. "
      ext y
      Hint (hidden := true) "Como antes, puedes simplificar la expresión. Puedes hacer varias
      simplificaciones de golpe con `simp [{hffi},{hggi}]`."
      simp [hffi,hggi]
