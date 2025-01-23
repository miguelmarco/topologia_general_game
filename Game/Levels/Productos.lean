import Game.Levels.Productos.ProductoIAN
Title "Productos"

Introduction "
En este mundo veremos cómo dotar de estructura de
espacio topológico al producto de dos espacios
topológicos.

Para ello, necesitamos alguna nociones sobre productos de conjuntos.

Si tenemos dos conjuntos (tipos) `X` e `Y`, el producto se denota como
`X × Y` (el símbolo `×` se teclea como `\\times`.), los objetos de `X × Y`
son de la forma `(x, y)`, donde `x : X` y `y : Y`.

Dado un elemento `z`  de `X × Y`, tiene dos componentes, que se denotan por
`z.1` y `z.2`. Además tenemos las aplicaciones proyección `π₁ : X × Y → X`
y `π₂ : X × Y → Y` que envian un elemento a sus componentes (es decir, `π₁ z = z.1`,
π₂ z = z.2`). `π₁` se teclea como `\\pi\\1`.

En ocasiones, estas notaciones se entremezclan haciendo que una expresión sea poco legible.
En ese caso, el simplificador puede ayudar.

Si tenemos subconjuntos `A ⊆ X` y `B ⊆ Y`, podemos considerar el correspondiente
subconjunto del producto `A ×ˢ B ⊆ X × Y` (fíjate en que para subconjuntos usamos
la operación `×ˢ`, que se teclea como `\\times\\^s`.)
"
