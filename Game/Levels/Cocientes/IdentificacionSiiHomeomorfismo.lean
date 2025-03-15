import Game.Levels.Cocientes.SupContCerIdent

World "Cocientes"
Level 15
Title "Identificaciones biyectivas."

Introduction "
Una aplicación biyectiva es una identificación si y solo si es un
homeomorfismo.
"

namespace topo
open topo espacio_topologico Set Function

variable {X: Type} [espacio_topologico X]

variable {Y : Type} [espacio_topologico Y]

/--
Una aplicación bijectiva entre espacios topológicos es
una identificación si y solo si es un homeomorfismo.
-/
TheoremDoc topo.identificacion_sii_homeomorfismo as "identificacion_sii_homeomorfismo" in "Cocientes"

Statement identificacion_sii_homeomorfismo (f : X → Y) (hf : Bijective f) :
    identificacion f ↔ homeomorfismo f := by
  Hint (hidden := true) "Puedes separar `{hf}` en dos
  afirmaciones con `choose` o `cases'`."
  choose hf1 hf2 using hf
  Hint (hidden := true) "Para poder hablar de homeomorfismo,
  necesitamos una función inversa `g : {X} → {Y}`.
  Gracias a `{hf2}`, podemos elegir un elemento de `{X}`
  para cada elemento de `{Y}`, y eso nos da la función
  que queremos, junto con su correspondiente propiedad.

  Así pues, elige esa función con `choose`."
  choose g hg using hf2
  Hint (hidden := true) "Ahora podemos reescribir el que
  `{f}` sea homeomorfismo en términos de que sea continua
  y abierta."
  rw [homeomorfismo_sii_continua_abierta]
  Hint (hidden := true) "Separa el objetivo en dos con
  `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Separa el objetivo en dos con
    `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes aplicar que las identificaciones
      son contínuas."
      apply identificacion_continua
      exact h
    · Hint (hidden := true) "Para ver que es abierta, tendrás
      que tomar un abierto arbitrario de `{Y}` con `intro`."
      intro U hU
      Hint (hidden := true) "Separa `{h}` en dos afirmaciones
      con `choose` o `cases'`."
      choose h1 h2 using h
      Hint (hidden := true) "Puedes reescribir el objetivo
      gracias a `{h2}`."
      rw [h2]
      Hint (hidden := true) "Puedes simplificar el objetivo
      gracias a `{hf1}`.

      Teclea `simp [{hf1}]`."
      simp only [hf1, preimage_image_eq]
      exact hU
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Separa `{h}` en dos afirmaciones
    con `choose` o `cases'`."
    choose h1 h2 using h
    Hint (hidden := true) "Puedes aplicar el teorema que te dice
    que una aplicación suprayectiva, continua y abierta
    es una identificación."
    apply sup_cont_abierta_ident
    · Hint (hidden := true) "Para ver que es suprayectiva,
      toma un elemento arbitrario de `{Y}` con `intro`."
      intro y
      Hint (hidden := true) "¿Qué elemento puedes usar?"
      use g y
      Hint (hidden := true) "Ahora puedes aplicar una afirmación que te
      asegura exactamente lo que quieres."
      apply hg
    · exact h1
    · exact h2
  · Hint "Para poder reescribir que `{f}` es un homeomorfismo
    si y solo si es continua y abierta, hemos tenido que suponer
    que hay una función inversa. Ahora tenemos que dar esa
    inversa y demostrar que, de hecho, es una inversa."
    exact g
  · Hint (hidden := true) "Para ver que dos aplicaciones son
    iguales, hay que ver que al aplicarlas a cualquier elmento
    dan el mismo resultado. Eso se hace con `ext`"
    ext y
    Hint (hidden := true) "Prueba a simplificar el objetivo."
    simp only [comp_apply, id_eq]
    Hint (hidden := true) "Puedes aplicar `{hg}`."
    rw [hg]
  · Hint (hidden := true) "De nuevo, necesitas usar `ext`
    para reducir el objetivo a ver que aplicar las funciones
    a un elemento arbitrario dan el mismo resultado."
    ext x
    Hint (hidden := true) "Observa que no podemos aplicar `{hg}`
    ya que la composición no va en el mismo orden.

    Lo que podemos hacer es usar que `{f}` es inyectiva
    para que baste ver que `{f} (({g} ∘ {f})  ̣{x}) = {f} (id {x})`."
    apply hf1
    Hint (hidden := true) "Ahora puedes simplificar el objetivo."
    simp only [comp_apply, id_eq]
    Hint (hidden := true) "Puedes aplicar `{hg}`."
    rw [hg]
