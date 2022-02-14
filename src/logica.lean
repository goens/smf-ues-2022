/-
Este documento ha sido escrito completamente como un archivo de Lean.
Para seguir los ejercicios, debe abrir este archivo en su editor,
por ejemplo VS Code. Se le deberían haber entregado instrucciones
de como instalar Lean en su computadora. En esta página puede
encontrar detalladas instrucciones, en inglés, de como instalar
Lean 3 en diferentes sistemas operativos:

https://leanprover-community.github.io/get_started.html
-/

/-
Se recomienda enfáticamente participar activamente en este curso:
no sólo escuche, pruebe también! 

Si de verdad intentó instalar Lean y no pudo por alguna razón,
una opción alternativa es ver esta hoja en línea:

https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fgoens%2Fsmf-ues-2022%2Fmaster%2Fsrc%2Flogica.lean

Sin embargo, se recomienda *no* acceder en línea, sino instalar
Lean en su computadora directamente. Así puede guardar su progreso
y en un futuro tal vez trabajar con teoremas más complejos también.
-/

/-
Esta primera hoja discute las bases de lógica en Lean.
La lógica es la base de la matemática moderna (axiomática). 

Si bien el estudio de la lógica puede ser complejo e interesante 
por su cuenta, en este minicurso no vamos a profundizar en temas
de lógica matemática. La idea de este primer módulo es aprender
sólo las bases de la lógica mínimas necesarias para usar Lean y
demostrar teoremas de otras ramas de la matemática.

Este minicurso está basado, en parte, en el curso "Formalizing
Mathematics" de Kevin Buzzard: 
https://github.com/ImperialCollegeLondon/formalising-mathematics
-/

/-
Antes de empezar con definiciones, creamos un espacio de nombres
para este curso, smf22. Este espacio lo usamos sólo para no tener
problemas de que usamos el mismo nombre que algo que ya exista.
-/
namespace smf22

/-
En la lógica los objetos principales de interés son "proposiciones"
Una proposición es un enunciado o una aseveración,
generalmente de una verdad demostrada o asumida, pero también de
una falsedad. A Lean le decimos que `P` es una proposición con la
notación usando dos puntos: `P : Prop`.

Por ejemplo:
-/
variables  (P Q R: Prop).

/- Esta declaración está diciendole a Lean que tenemos tres variables,
`P`, `Q` y `R`. Estas tres variables representan propoiciones.
Podrían ser proposiciones como "todos los hombres son mortales" o
"Socrates es un hombre", ejemplos clásicos de la lógica, pero también
proposiciones matemáticas como "2 es el único número primo par" 
o incluso "La parte real de todo cero no trivial de la función 
zeta de Riemann es `1/2`". 

En la lógica no importa lo que estas proposiciones representan.
Lo que importa son sus relaciones, como implicación.
En las matemáticas, generalmente escribimos `P ⇒ Q` para
decir que `P` implica `Q`. En Lean se usa la flecha sencilla,
`P → Q`, por razones que van más allá de este minicurso (tiene 
que ver con un concepto llamado la correspondencia de Curry-Howard,
pero no profundizaremos en esto).  -/

/-
Empezamos demostrando un teorema bien sencillo, para entender
como funciona Lean y como nos ayuda a demostrar. Toda proposición
`P` se implica a si misma. En Lean lo decimos de la siguiente manera:
-/
theorem id : P → P :=
begin
 intro hP,
 exact hP,
end

/-
Para demostrar esto usamos dos "tácticas", `intro` que introduce
hipótesis, y `exact` que le dice a Lean que nuestra solución es
exactamente la hipótesis nombrada.

Un ejemplo un poco menos trivial, conocido como "modus ponens"
  en lógica, que viene del latín: "el modo que, al afirmar, afirma"
-/
lemma modus_ponens : P → (P → Q) → Q := 
begin
  intros hP hPQ,
  apply hPQ,
  exact hP,
end

/- 
La táctica `intro` se puede usar para introducir varias
hipótesis a la vez, diciendo en vez `intros`.

Aquí también hemos usado una nueva táctica, `apply`. 
Esta reduce nuestro *objetivo* usando una suposición.
Note como esto nos sirve para razonar "para atrás": 

Para demostrar `Q`, sabiendo que `P → Q`, basta demostrar
`P`. En las matemáticas es más común razonar "para adelante":
-/
lemma modus_ponens_adelante : P → (P → Q) → Q := 
begin
  intros hP hPQ,
  have hQ := hPQ hP,
  exact hQ,
end

/- Al usar `have` le podemos dar nombre a una conclusión que
tenemos, en el estilo de razonamiento "hacia adelante". Sin 
embargo, trabjando en Lean preferimos la otra variante, reduciendo
el objectivo. -/

/- Empezamos con el primer ejercicio para resolver, demostremos
que la implicación lógica es transitiva -/
lemma imp_trans : (P → Q) → (Q → R) → (P → R) :=
begin
  sorry
end

/- Le decimos a Lean que no tenemos una demostración usando
`sorry`, como disculpa, para que acepte el teorema sin demostación.
No se preocupe, sin embargo, Lean advierte cuando un teorema ha sido
aceptado sin demostración, también cuando hemos usado un teorema que
ya teníamos. -/

-- El siguiente us una variante "relativa" del "modus ponens".
 -- Asumiendo `P`, si `Q -> R` y `Q`, entonces `R`.
lemma forall_imp : (P → Q → R) → (P → Q) → (P → R) :=
begin
  -- `intros hPQR hPQ hP,` sería una forma rápida de comenzar.
  -- Asegúrese de entender que está pasando aquí si la usa.
  sorry
end

/-
Hemos visto implicación lógica. El siguiente concepto central
que veremos es la negación.

La negación de `P` se escribe `¬ P`. En Lean, esto es *por definición*
equivalente a decir `P → false`. El origen de esto es el concepto
en lógica de "Ex falso quodlibet", de la falsedad se puede deducir
calquier cosa. Entonces una proposicicón `P` es falsa si (y sólo si)
podemos deducir also falso de ella. Esto nunca pasa con una 
proposición verdadera, o si no nuestros axiomas fueran inconsistentes!

En Lean podemos escribir esta caracterización de la siguiente manera:
-/
theorem not_iff_imp_false : ¬ P ↔ (P → false) :=
begin
  -- por definición
  refl
end

/-
Hemos escrito `↔` en vez de `→`, para decir "si y sólo si". 
`P ↔ Q` no quiere decir más que `P → Q` y `Q → P`.

Para demostrarlo usamos una nueva táctia, `refl`, que quiere
decir que por "reflexividad" (de la equivalencia). Básicamente
le estamos diciendo esto es verdad porque ambos lados dicen lo
mismo.

Vamos a demostrar la doble negación, de la siguiente manera:
-/
theorem not_not_intro : P → ¬ (¬ P) :=
begin
  intro hP,
  rw not_iff_imp_false,
  -- Podemos usar `rw not_iff_imp_false` para cambiar `¬ X` a `X → false`. 
  -- Pero no tenemos que hacerlo porque son lo mismo *por definición*
  sorry,
end

/-
La táctica `rw` viene de "rewrite" (reescribir, en inglés). 
La usamos para cambiar dos porposiciónes que son equivalentes,
o dos valores que son iguales, en alguna hipótesis u objetivo.
-/

/-
La otra implicación, `¬ (¬ P) → P` no la podemos demostrar aquí.
De hecho, esto es equivalente a un axioma que se llama el
 "principio del tercero excluido":
-/
axiom te (A : Prop) : A ∨ ¬ A

/-
Discutiremos esto más tarde, después de hablar de disyunciones.
-/

/- Relacionado con el anterior, vamos a demostrar otro principio 
de razonamiento lócigo que normalmente se le concoce como 
"modus tollens". A veces se le considera una forma de 
"demostración por contradicción": -/

theorem modus_tollens : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry,
end

/-
Para demostrar la porposición de "ex falso quod libet"
  mencionada arriba
-/
theorem ex_falso_quod_libet : false → Q :=
begin
  intros hFalse,
  exfalso,
  exact hFalse,
end

/- Esta demostración ocupa una tactica 'exfalso'
para cambiar el objectivo a "false" (falso).
Podemos hacer esto porque (asumimos que) a partir de nuestros 
axiomas no se puede demostrar falso. 

Entonces en este caso podemos deducir cualquier cosa, 
pero obviamente la premisa (falso) nunca se cumplirá.
Recuerde que aquí estamos demostrando la *implicación*
`false → Q`, y no la proposición `Q` sola. 
 -/

/-
A continuación vamos a cubrir conjunciones (el "y" lógico).
En Lean, igual que en lógica, escribimos una conjunción con el
símbolo `∧`. 

En Lean, la hipótesis `P ∧ Q` es equivalente a tener dos
hipótesis, `P` y `Q`. Podemos separarlas usando la táctica
`cases`:
-/

theorem and.elim_left : P ∧ Q → P :=
begin
  intros hPyQ,
  cases hPyQ with hP hQ,
  exact hP,
end

/- Ahora un exercicio muy sencillo! -/
theorem and.elim_right : P ∧ Q → Q :=
begin
  sorry
end

/- Hemos visto como usar una hipótesis con una conjunción.
 Ahora, para *demostrar* una proposición con una conjución,
 tenemos que demostrar que amabs proposiciones son verdaderas.
 Esto lo hacemos con la táctica `split`: -/

theorem and.intro : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  { --usamos estos parentesis curvos para 'enfocar' un objetivo.
     exact hP,
  },
  {
     exact hQ,
   }
end

/- Un par de ejercicios: -/
theorem and.elim : P ∧ Q → (P → Q → R) → R :=
begin
  sorry,
end

/-- `∧` es simétrico -/
theorem and.symm : P ∧ Q → Q ∧ P :=
begin
  sorry
end

/-- `∧` es transitivo -/
theorem and.trans : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  sorry,
end

/- Luego de ver la conjunción, vamos a ver la disyunción. 
Para esto necesitaremos una variable más, `S`, que también
sea una proposición:
-/
variable (S : Prop)

/- Igual que con la conjunción, es diferente como demostrar
una disyunción a como usarla en una demostración: -/

theorem or.intro_left : P → P ∨ Q :=
begin
  intros hP,
  left,
  exact hP,
end

/- La táctica `left` (izquierda en inglés) se usa para escoger
la parte izquierda de una disjyunción. Equivalentamente podemos
demostrar escogiendo la derecha con la táctica `right`. Intente
demostrar lo siguiente: -/
theorem or.intro_right : Q → P ∨ Q :=
begin
  sorry,
end

/- Como usamos una disyunción en una hipótesis? 
  Igual que vimos anteriormente, distinguiendo 
  diferentes casos con la táctica `cases` -/
theorem or.elim : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros hPoQ, 
  cases hPoQ with hP hQ,
  {
   intros hPR hQR,
   apply hPR,
   exact hP,
  },
  {
   intros hPR hQR,
   apply hQR,
   exact hQ,
  }
end

/- Cual es la diferencia entre el uso de `cases` aquí en 
disyunción y anteriormente en una conjunción? -/

/- Un par de ejercicios de propiedades de la disyunción: -/
/- `∨` es simétrico -/
theorem or.symm : P ∨ Q → Q ∨ P :=
begin
  sorry
end

/- `∨` is commutativo -/
theorem or.comm : P ∨ Q ↔ Q ∨ P :=
begin
  sorry,
end

/- `∨` is associativo -/
theorem or.assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
begin
  sorry,
end

/-
Finalmente, regresamos al principio del tercero
excluido. Puede demostrar la otra dirección de
la doble negación que vimos anteriormente?

Recuerde que *necesita* usar el axioma `te`
que definimos arriba. 

Podemos pedirle a Lean que nos lo recuerde
usando `#check`:
-/
#check te

/-
Aquí usamos `have` para incluir la hipótesis que
obtenemos del axioma explicitamente en nuestra
demostración:
-/
theorem eliminacion_de_doble_negacion : ¬ (¬ P) → P :=
begin
  have hPonoP := (te P),
  sorry,
end


end smf22
