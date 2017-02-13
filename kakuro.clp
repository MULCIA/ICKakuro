;;; IC: Trabajo (2016/2017)
;;; Resolucion deductiva de un Kakuro
;;; Departamento de Ciencias de la Computacion e Inteligencia Artificial 
;;; Universidad de Sevilla
;;;============================================================================


;;;============================================================================
;;; Representacion del Kakuro
;;;============================================================================

;;;   Utilizaremos la siguiente plantilla para representar las celdas del
;;; Kakuro. Cada celda tiene los siguientes campos:
;;; - id: Identificador unico de la celda
;;; - fila: Numero de fila en la que se encuentra la celda
;;; - columna: Numero de columna en la que se encuentra la celda
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores numericos de 1 a 9.

(deftemplate celda
  (slot id)
  (slot fila)
  (slot columna)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))

;;;   De esta forma, una celda tendra un valor asignado si y solo si dicho
;;; valor es el unico elemento del rango.

;;;   La siguiente variable global sirve enumerar las restricciones del puzle.

(defglobal ?*restricciones* = 0)

;;;   La siguiente funcion sirve para asignar de forma automatica y unica
;;; identificadores a las restricciones del puzle. 

(deffunction idRestriccion ()
  (bind ?*restricciones* (+ ?*restricciones* 1))
  ?*restricciones*)

;;;   Utilizaremos la siguiente plantilla para almacenar las restricciones del
;;; puzle. Cada restriccion tiene los siguientes campos:
;;; - id: Identificador unico de la restriccion
;;; - valor: Valor de la restriccion
;;; - casillas: Identificadores de las casillas que se ven afectadas por la
;;;   restriccion

(deftemplate restriccion
  (slot id
        (default-dynamic (idRestriccion)))
  (slot valor)
  (multislot casillas))

;;;============================================================================
;;; Estrategias de resolucion
;;;============================================================================

;;;   El objetivo del trabajo consiste en implementar un conjunto de reglas
;;; CLIPS que resuelvan un Kakuro de forma deductiva, es decir, deduciendo el
;;; valor de una casilla a partir de reglas que analicen los posibles valores
;;; de las casillas relacionadas.




;;;============================================================================
;;; Reglas para imprimir el resultado
;;;============================================================================

;;;   Las siguientes reglas permiten visualizar el estado del puzle, una vez
;;; aplicadas todas las reglas que implementan las estrategias de resolucion.
;;; La prioridad de estas reglas es -10 para que sean las ultimas en
;;; aplicarse.

;;;   Para las casillas del tablero con un unico valor en su rango se indica
;;; dicho valor, para las casillas del tablero en las que no se haya podido
;;; deducir el valor se indica el simbolo '?'. El resto de las casillas hasta
;;; completar la cuadricula 9x9 se dejan en blanco.

(defrule imprime-solucion
  (declare (salience -10))
  =>
  (printout t "+---------+" crlf "|")
  (assert (imprime 1 1)))

(defrule imprime-celda-1
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (celda (fila ?i) (columna ?j) (rango $?v))
  =>
  (retract ?h)
  (if (= (length$ $?v) 1)
      then (printout t (nth$ 1 $?v))
    else (printout t "?"))
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

(defrule imprime-celda-2
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (not (celda (fila ?i) (columna ?j) (rango $?v)))
  =>
  (retract ?h)
  (printout t " ")
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

;;;============================================================================
;;; Funcionalidad para leer los puzles del fichero de ejemplos
;;;============================================================================

;;;   Esta funcion crea una lista de identificadores de casillas en horizontal.

(deffunction crea-casillas-horizontal (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat ?f (+ ?c ?i))))))
  ?datos)

;;;   Esta funcion construye los hechos que representan las restricciones de
;;; una linea horizontal del Kakuro.

(deffunction procesa-restricciones-fila (?f $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?c ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?c))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-horizontal ?f ?c (- ?i ?c)))))))
  TRUE)

;;;   Esta funcion crea una lista de identificadores de casillas en vertical.

(deffunction crea-casillas-vertical (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat (+ ?f ?i) ?c)))))
  ?datos)

;;;   Esta funcion construye los hechos que representan las restricciones de
;;; una linea horizontal del Kakuro.

(deffunction procesa-restricciones-columna (?c $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?f ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?f))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-vertical ?f ?c (- ?i ?f)))))))
  TRUE)

;;;   Esta funcion construye todos los hechos que representan las restricciones
;;; de un Kakuro dado en el formato utilizado en el fichero de ejemplos.

(deffunction procesa-restricciones-ejemplo (?datos)
  (loop-for-count
   (?i 1 9)
   (bind $?linea (create$))
   (loop-for-count
    (?j 2 10)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-fila ?i ?linea))
  (loop-for-count
   (?j 2 10)
   (bind $?linea (create$))
   (loop-for-count
    (?i 1 9)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-columna (- ?j 1) ?linea))
  TRUE)

;;;   Esta funcion localiza el Kakuro que se quiere resolver en el fichero de
;;; ejemplos.

(deffunction lee-kakuro (?n)
  (open "ejemplos.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
                  (readline data))
  (bind ?datos (readline data))
  (procesa-restricciones-ejemplo ?datos)
  (close data))

;;;   Esta regla pregunta al usuario que numero de Kakuro del fichero de
;;; ejemplos se quiere resolver y genera los hechos que representan las
;;; restricciones asociadas.

(defrule kakuro-numero
  (declare (salience 100))
  =>
  (printout t "Que problema quieres resolver (1-50)? : ")
  (lee-kakuro (read)))

;;;   Esta regla construye las celdas que aparecen en alguna de las
;;; restricciones del Kakuro que se quiere resolver.

(defrule crea-celdas-restricciones
  (declare (salience 100))
  (restriccion (casillas $? ?id $?))
  (not (celda (id ?id)))
  =>
  (assert (celda (id ?id) (fila (div ?id 10)) (columna (mod ?id 10)))))

;;;============================================================================
;;; Reglas para resolver el Kakuro
;;;============================================================================

;;;============================================================================
;;; Reglas basicas
;;;============================================================================

;;; Si hay una celda que tiene una unica restriccion y su valor es <= 9,
;;; solucionar celda asignando el valor de la restriccion.
(defrule restriccion-con-unica-casilla
  (declare (salience 90))
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas ?c))
  ?h2 <- (celda (id ?i&:(eq ?i ?c)) (rango $?))
  =>
  (modify ?h2
          (rango ?v)))

;;; Si hay celdas que tienen una restriccion <= 9, dejar en el rango de valores
;;; de la celda el rango de valores desde 1 hasta el valor de la restriccion 
;;; menos 1.
(defrule eliminar-no-candidatos
  (declare (salience 90))
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas $? ?c $?))
  ?h2 <- (celda (id ?i&:(eq ?i ?c))  (rango $?ini ?r&:(eq ?r ?v) $?))
  =>
  (modify ?h2
          (rango $?ini)))

;;; Si hay una restriccion par y valor <= 18, en sus casillas no puede estar 
;;; el valor/2. Por ejemplo, restriccion 4 no se puede resolver con un valor 2
;;; en ninguna casilla.
(defrule eliminar-valor-entre-2-si-par-menor-igual-18
  (declare (salience 80))
  ?h1 <- (restriccion (valor ?v&:(and (eq (mod ?v 2) 0) (<= ?v 18))) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (rango $?ini ?r&:(eq ?r (div ?v 2)) $?fin))
  =>
  (modify ?h2
          (rango $?ini $?fin)))

;;; Si en un grupo de celdas para una restriccion ya hay una resuelta, eliminar 
;;; dicho valor del rango del resto de casillas a las que aplica la misma restriccion

;;; TODO

;;;(defrule eliminar-asignados-celdas-vecinas
;;;  ?h1 <- (restriccion (valor ?v) (casillas $?ini ?j $?fin))
;;;  ?h2 <- (celda (id ?i&:(eq ?i ?j)) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
;;;  ?h3 <- (celda (id ?k&:(neq ?k ?i)) (rango $?inih3 ?r2&:(eq ?r2 ?r1) $?finh3))
;;;  (test (and (eq (length $?inih2) 0) (eq (length $?finh2) 0)))
;;;  (test (or (> (length $?inih3) 1) (> (length $?finh3) 1)))
;;;  (test (or (member ?k $?ini) (member ?k $?fin)))
;;;  =>
;;;  (modify ?h3
;;;          (rango $?inih3 $?finh3)))

(defrule eliminar-asignados-fila
  ?h1 <- (restriccion (valor ?v) (casillas $?ini ?j $?fin))
  ?h2 <- (celda (id ?i&:(eq ?i ?j)) (fila ?f1) (columna ?c1) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?k&:(neq ?k ?i)) (fila ?f2&:(eq ?f2 ?f1)) (columna ?c2&:(neq ?c2 ?c1)) (rango $?inih3 ?r2&:(eq ?r2 ?r1) $?finh3))
  (test (and (eq (length $?inih2) 0) (eq (length $?finh2) 0)))
  (test (or (> (length $?inih3) 0) (> (length $?finh3) 0)))
  (test (or (member ?k $?ini) (member ?k $?fin)))
  =>
  (modify ?h3
          (rango $?inih3 $?finh3)))

;;; Hay celdas en una columna que solo tienen un valor en su rango, eliminar 
;;; dicho valor del rango del resto de celdas de la misma columna.
(defrule eliminar-asignados-columna
  ?h1 <- (restriccion (valor ?v) (casillas $?ini ?j $?fin))
  ?h2 <- (celda (id ?i&:(eq ?i ?j)) (fila ?f1) (columna ?c1) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?k&:(neq ?k ?i)) (fila ?f2&:(neq ?f2 ?f1)) (columna ?c2&:(eq ?c2 ?c1)) (rango $?inih3 ?r2&:(eq ?r2 ?r1) $?finh3))
  (test (and (eq (length $?inih2) 0) (eq (length $?finh2) 0)))
  (test (or (> (length $?inih3) 0) (> (length $?finh3) 0)))
  (test (or (member ?k $?ini) (member ?k $?fin)))
  =>
  (modify ?h3
          (rango $?inih3 $?finh3)))

;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 2 celdas
;;;============================================================================

;;; Grupos de dos casillas que tienen una de las dos resuelta, la solucion es 
;;; restar a la restriccion y, el resultado, asignarlo a la otra celda.

(defrule resolver-fila-2cas
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?fh2) (columna ?ch2) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?fh3&:(eq ?fh3 ?fh2)) (columna ?ch3&:(neq ?ch3 ?ch2)) (rango $?inih3 ?r2&:(<= ?r2 ?v) $?finh3))
  (test (neq ?i ?j))
  (test (and (eq (length $?inih2) 0) (eq (length $?finh2) 0)))
  (test (or (> (length $?inih3) 0) (> (length $?finh3) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (- ?v ?r1) ?r2))
  =>
  (modify ?h3
          (rango ?r2)))

(defrule resolver-columna-2cas
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?fh2) (columna ?ch2) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?fh3&:(neq ?fh3 ?fh2)) (columna ?ch3&:(eq ?ch3 ?ch2)) (rango $?inih3 ?r2&:(<= ?r2 ?v) $?finh3))
  (test (neq ?i ?j))
  (test (and (eq (length $?inih2) 0) (eq (length $?finh2) 0)))
  (test (or (> (length $?inih3) 0) (> (length $?finh3) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (- ?v ?r1) ?r2))
  =>
  (modify ?h3
          (rango ?r2)))

(defrule resolver-conjunto-2cas-fila-mayor-9
  ?h1 <- (restriccion (valor ?v&:(> ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?fh2) (columna ?ch2) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?fh3&:(eq ?fh3 ?fh2)) (columna ?ch3&:(neq ?ch3 ?ch2)) (rango $?inih3 ?r2&:(<= ?r2 ?v) $?finh3))
  (test (neq ?i ?j))
  (test (and (eq (length $?inih2) 0) (eq (length $?finh2) 0)))
  (test (or (> (length $?inih3) 0) (> (length $?finh3) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (+ ?r1 ?r2) ?v))
  =>
  (modify ?h3
        (rango ?r2)))

(defrule resolver-conjunto-2cas-columna-mayor-9
  ?h1 <- (restriccion (valor ?v&:(> ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?fh2) (columna ?ch2) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?fh3&:(neq ?fh3 ?fh2)) (columna ?ch3&:(eq ?ch3 ?ch2)) (rango $?inih3 ?r2&:(<= ?r2 ?v) $?finh3))
  (test (neq ?i ?j))
  (test (and (eq (length $?inih2) 0) (eq (length $?finh2) 0)))
  (test (or (> (length $?inih3) 0) (> (length $?finh3) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (+ ?r1 ?r2) ?v))
  =>
  (modify ?h3
        (rango ?r2)))

;;;============================================================================

;;; Una restriccion cuyo valor es <= 18 y que aplique a exactamente 2 celdas, probar todas las combinaciones
;;; y dejar solo auqellas cuyo resultado de sumar dos valores sea exactmente el valor de la restriccion
(defrule probar-candidatos-dos-celdas
  (declare (salience -5))
  ?h1 <- (restriccion (valor ?v&:(<= ?v 18)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i1&:(or (eq ?i1 ?c1) (eq ?i1 ?c2))) (rango $?rango1))
  ?h3 <- (celda (id ?i2&:(or (eq ?i2 ?c1) (eq ?i2 ?c2))) (rango $?rango2))
  (test (neq ?i1 ?i2))
  (test (> (length $?rango1) 1))
  (test (> (length $?rango2) 1))
  =>
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (eq ?v (+ ?a ?b))
        then (printout t "Result: " (+ ?a ?b) " , value: " ?v crlf)
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h3 (rango ?candidate2))
  )
)

;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 3 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 3 casillas, y dos de ellas estan resueltas
;;; aplicar a la resultante la resta del valor de la restriccion con los dos valores asignados
(defrule resolver-3cas-2resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  (test (> (length $?r1) 1))
  =>
  (bind ?res (- ?v (+ ?r2 ?r3)))
  (if (<= ?res 9)
    then (modify ?h2 (rango ?res))
  )
)

(defrule resolver-3cas-2resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  (test (> (length $?r2) 1))
  =>
  (bind ?res (- ?v (+ ?r1 ?r3)))
  (if (<= ?res 9)
    then (modify ?h3 (rango ?res))
  )
)

(defrule resolver-3cas-2resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  (test (> (length $?r3) 1))
  =>
  (bind ?res (- ?v (+ ?r1 ?r2)))
  (if (<= ?res 9)
    then (modify ?h4 (rango ?res))
  )
)

;;;============================================================================

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-3cas-1resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  (test (> (length $?r2) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r2)
  (bind $?rango2 $?r3)
  (bind ?v (- ?v ?r1))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-3cas-1resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  (test (> (length $?r1) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r3)
  (bind ?v (- ?v ?r2))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-3cas-1resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  (test (> (length $?r1) 1))
  (test (> (length $?r2) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r2)
  (bind ?v (- ?v ?r3))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h3 (rango ?candidate2))
  )
)

;;;============================================================================

;;; Si una restriccion aplica sobre 3 casillas, probar combinaciones y asingar
;;; si solo hay una posible
(defrule resolver-3cas-0resueltas
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  (test (> (length $?r1) 1))
  (test (> (length $?r2) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r2)
  (bind $?rango3 $?r3)
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?candidate3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      	(while (<= ?k (length $?rango3))
      		(bind ?c (nth$ ?k $?rango3))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidate1 ?a) 
             		(bind ?candidate2 ?b) 
             		(bind ?candidate3 ?c) 
      		)
      		(bind ?k (+ ?k 1))
      	)
      (bind ?j (+ ?j 1))
      (bind ?k 1)
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h3 (rango ?candidate2))
         (modify ?h4 (rango ?candidate3))
  )
)

;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 4 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; aplicar a la resultante la resta del valor de la restriccion con los dos valores asignados
(defrule resolver-4cas-3resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  (test (> (length $?r1) 1))
  =>
  (bind ?res (- ?v (+ ?r2 (+ ?r3 ?r4))))
  (if (<= ?res 9)
    then (modify ?h2 (rango ?res))
  )
)

(defrule resolver-4cas-3resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  (test (> (length $?r2) 1))
  =>
  (bind ?res (- ?v (+ ?r1 (+ ?r3 ?r4))))
  (if (<= ?res 9)
    then (modify ?h3 (rango ?res))
  )
)

(defrule resolver-4cas-3resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  (test (> (length $?r3) 1))
  =>
  (bind ?res (- ?v (+ ?r1 (+ ?r2 ?r4))))
  (if (<= ?res 9)
    then (modify ?h4 (rango ?res))
  )
)

(defrule resolver-4cas-3resueltas-4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  (test (> (length $?r4) 1))
  =>
  (bind ?res (- ?v (+ ?r1 (+ ?r2 ?r3))))
  (if (<= ?res 9)
    then (modify ?h5 (rango ?res))
  )
)

;;;============================================================================

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-2resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  (test (> (length $?r3) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r3)
  (bind $?rango2 $?r4)
  (bind ?v (- ?v (+ ?r1 ?r2)))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h4 (rango ?candidate1))
         (modify ?h5 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-2resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  (test (> (length $?r2) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r2)
  (bind $?rango2 $?r3)
  (bind ?v (- ?v (+ ?r1 ?r4)))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-2resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  (test (> (length $?r2) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r2)
  (bind $?rango2 $?r4)
  (bind ?v (- ?v (+ ?r1 ?r3)))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidate1))
         (modify ?h5 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-2resueltas-4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  (test (> (length $?r1) 1))
  (test (> (length $?r2) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r2)
  (bind ?v (- ?v (+ ?r3 ?r4)))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h3 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-2resueltas-5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  (test (> (length $?r1) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r3)
  (bind ?v (- ?v (+ ?r2 ?r4)))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-2resueltas-6
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  (test (> (length $?r1) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r4)
  (bind ?v (- ?v (+ ?r2 ?r3)))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h5 (rango ?candidate2))
  )
)

;;;============================================================================

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-1resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  (test (> (length $?r1) 1))
  (test (> (length $?r2) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r2)
  (bind $?rango3 $?r3)
  (bind ?v (- ?v ?r4))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?candidate3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      	(while (<= ?k (length $?rango3))
      		(bind ?c (nth$ ?k $?rango3))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidate1 ?a) 
             		(bind ?candidate2 ?b) 
             		(bind ?candidate3 ?c) 
      		)
      		(bind ?k (+ ?k 1))
      	)
      (bind ?j (+ ?j 1))
      (bind ?k 1)
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h3 (rango ?candidate2))
         (modify ?h4 (rango ?candidate3))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-1resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  (test (> (length $?r1) 1))
  (test (> (length $?r2) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r2)
  (bind $?rango3 $?r4)
  (bind ?v (- ?v ?r3))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?candidate3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      	(while (<= ?k (length $?rango3))
      		(bind ?c (nth$ ?k $?rango3))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidate1 ?a) 
             		(bind ?candidate2 ?b) 
             		(bind ?candidate3 ?c) 
      		)
      		(bind ?k (+ ?k 1))
      	)
      (bind ?j (+ ?j 1))
      (bind ?k 1)
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h3 (rango ?candidate2))
         (modify ?h5 (rango ?candidate3))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-1resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  (test (> (length $?r1) 1))
  (test (> (length $?r3) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r3)
  (bind $?rango3 $?r4)
  (bind ?v (- ?v ?r2))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?candidate3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      	(while (<= ?k (length $?rango3))
      		(bind ?c (nth$ ?k $?rango3))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidate1 ?a) 
             		(bind ?candidate2 ?b) 
             		(bind ?candidate3 ?c) 
      		)
      		(bind ?k (+ ?k 1))
      	)
      (bind ?j (+ ?j 1))
      (bind ?k 1)
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
         (modify ?h5 (rango ?candidate3))
  )
)

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-4cas-1resueltas-4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  (test (> (length $?r2) 1))
  (test (> (length $?r3) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r2)
  (bind $?rango2 $?r3)
  (bind $?rango3 $?r4)
  (bind ?v (- ?v ?r1))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?candidate3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      	(while (<= ?k (length $?rango3))
      		(bind ?c (nth$ ?k $?rango3))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidate1 ?a) 
             		(bind ?candidate2 ?b) 
             		(bind ?candidate3 ?c) 
      		)
      		(bind ?k (+ ?k 1))
      	)
      (bind ?j (+ ?j 1))
      (bind ?k 1)
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
         (modify ?h5 (rango ?candidate3))
  )
)

;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 5 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; aplicar a la resultante la resta del valor de la restriccion con los dos valores asignados
(defrule resolver-5cas-4resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r1) 1))
  =>
  (bind ?res (- ?v (+ ?r2 (+ ?r3 (+ ?r4 ?r5)))))
  (if (<= ?res 9)
    then (modify ?h2 (rango ?res))
  )
)

(defrule resolver-5cas-4resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r2) 1))
  =>
  (bind ?res (- ?v (+ ?r1 (+ ?r3 (+ ?r4 ?r5)))))
  (if (<= ?res 9)
    then (modify ?h3 (rango ?res))
  )
)

(defrule resolver-5cas-4resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r3) 1))
  =>
  (bind ?res (- ?v (+ ?r1 (+ ?r2 (+ ?r4 ?r5)))))
  (if (<= ?res 9)
    then (modify ?h4 (rango ?res))
  )
)

(defrule resolver-5cas-4resueltas-4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r4) 1))
  =>
  (bind ?res (- ?v (+ ?r1 (+ ?r2 (+ ?r3 ?r5)))))
  (if (<= ?res 9)
    then (modify ?h5 (rango ?res))
  )
)

(defrule resolver-5cas-4resueltas-5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango $?r5))
  (test (> (length $?r5) 1))
  =>
  (bind ?res (- ?v (+ ?r1 (+ ?r2 (+ ?r3 ?r4)))))
  (if (<= ?res 9)
    then (modify ?h6 (rango ?res))
  )
)

;;;============================================================================

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r1) 1))
  (test (> (length $?r2) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r2)
  (bind ?v (- ?v (+ ?r3 (+ ?r4 ?r5))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h3 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r1) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r3)
  (bind ?v (- ?v (+ ?r2 (+ ?r4 ?r5))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r1) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r4)
  (bind ?v (- ?v (+ ?r2 (+ ?r3 ?r5))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h5 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango $?r5))
  (test (> (length $?r1) 1))
  (test (> (length $?r5) 1))
  =>
  (bind $?rango1 $?r1)
  (bind $?rango2 $?r5)
  (bind ?v (- ?v (+ ?r2 (+ ?r3 ?r4))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidate1))
         (modify ?h6 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r2) 1))
  (test (> (length $?r3) 1))
  =>
  (bind $?rango1 $?r2)
  (bind $?rango2 $?r3)
  (bind ?v (- ?v (+ ?r1 (+ ?r4 ?r5))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidate1))
         (modify ?h4 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-6
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r2) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r2)
  (bind $?rango2 $?r4)
  (bind ?v (- ?v (+ ?r1 (+ ?r3 ?r5))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidate1))
         (modify ?h5 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-7
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango $?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango $?r5))
  (test (> (length $?r2) 1))
  (test (> (length $?r5) 1))
  =>
  (bind $?rango1 $?r2)
  (bind $?rango2 $?r5)
  (bind ?v (- ?v (+ ?r1 (+ ?r3 ?r4))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidate1))
         (modify ?h6 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-8
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango ?r5))
  (test (> (length $?r3) 1))
  (test (> (length $?r4) 1))
  =>
  (bind $?rango1 $?r3)
  (bind $?rango2 $?r4)
  (bind ?v (- ?v (+ ?r1 (+ ?r2 ?r5))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h4 (rango ?candidate1))
         (modify ?h5 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-9
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango $?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango ?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango $?r5))
  (test (> (length $?r3) 1))
  (test (> (length $?r5) 1))
  =>
  (bind $?rango1 $?r3)
  (bind $?rango2 $?r5)
  (bind ?v (- ?v (+ ?r1 (+ ?r2 ?r4))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h4 (rango ?candidate1))
         (modify ?h6 (rango ?candidate2))
  )
)

;;; Si una restriccion aplica sobre 3 casillas, y una de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible
(defrule resolver-5cas-3resueltas-10
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango ?r1))
  ?h3 <- (celda (id ?j&:(eq ?j ?c2)) (rango ?r2))
  ?h4 <- (celda (id ?k&:(eq ?k ?c3)) (rango ?r3))
  ?h5 <- (celda (id ?l&:(eq ?l ?c4)) (rango $?r4))
  ?h6 <- (celda (id ?m&:(eq ?m ?c5)) (rango $?r5))
  (test (> (length $?r4) 1))
  (test (> (length $?r5) 1))
  =>
  (bind $?rango1 $?r4)
  (bind $?rango2 $?r5)
  (bind ?v (- ?v (+ ?r1 (+ ?r2 ?r3))))
  (bind ?candidate1 0)
  (bind ?candidate2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length $?rango1))
    (bind ?a (nth$ ?i $?rango1))
    (while (<= ?j (length $?rango2))
      (bind ?b (nth$ ?j $?rango2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidate1 ?a) 
             (bind ?candidate2 ?b) 
      )
      (bind ?j (+ ?j 1))
    )
    (bind ?i (+ ?i 1))
    (bind ?j 1)
  )
  (if (eq ?cont 1)
    then (modify ?h5 (rango ?candidate1))
         (modify ?h6 (rango ?candidate2))
  )
)


;;;============================================================================
;;; Reglas que aplican en bloques magicos
;;;============================================================================

;;; Reglas para encontrar bloques magicos, que son bloques que nos ayudan a
;;; eliminar candidatos y encontrar posibilidades de resolucion con 
;;; reglas de interseccion

;;; BM - Elimina valor distintos de 1 y 2 para celdas con restriccion 3 y
;;; numero de casillas 2
(defrule bloque-magico-sum3-2cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 3)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum3-2cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 3)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 1 y 3 para celdas con restriccion 4 y
;;; numero de casillas 2
(defrule bloque-magico-sum4-2cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 4)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum4-2cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 4)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 7 y 9 para celdas con restriccion 16 y
;;; numero de casillas 2
(defrule bloque-magico-sum16-2cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 7) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum16-2cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 7) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 8 y 9 para celdas con restriccion 17 y
;;; numero de casillas 2
(defrule bloque-magico-sum17-2cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 17)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum17-2cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 17)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 1, 2 y 3 para celdas con restriccion 6 y
;;; numero de casillas 3
(defrule bloque-magico-sum6-3cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 6)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum6-3cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 6)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum6-3cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 6)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 1, 2 y 4 para celdas con restriccion 7 y
;;; numero de casillas 3
(defrule bloque-magico-sum7-3cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 7)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum7-3cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 7)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum7-3cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 7)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 6, 8 y 9 para celdas con restriccion 23 y
;;; numero de casillas 3
(defrule bloque-magico-sum23-3cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 23)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 6) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum23-3cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 23)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 6) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum23-3cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 23)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 6) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 7, 8 y 9 para celdas con restriccion 24 y
;;; numero de casillas 3
(defrule bloque-magico-sum24-3cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 24)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum24-3cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 24)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum24-3cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 24)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 1, 2, 3 y 4 para celdas con restriccion 10 y
;;; numero de casillas 4
(defrule bloque-magico-sum10-4cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 10)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum10-4cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 10)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum10-4cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 10)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum10-4cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 10)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 1, 2, 3 y 5 para celdas con restriccion 11 y
;;; numero de casillas 4
(defrule bloque-magico-sum11-4cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 11)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum11-4cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 11)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum11-4cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 11)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum11-4cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 11)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 5, 7, 8 y 9 para celdas con restriccion 29 y
;;; numero de casillas 4
(defrule bloque-magico-sum29-4cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-4cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-4cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-4cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 6, 7, 8 y 9 para celdas con restriccion 30 y
;;; numero de casillas 4
(defrule bloque-magico-sum30-4cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 30)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum30-4cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 30)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum30-4cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 30)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum30-4cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 30)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 1, 2, 3, 4 y 5 para celdas con restriccion 15 y
;;; numero de casillas 5
(defrule bloque-magico-sum15-5cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 15)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum15-5cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 15)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum15-5cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 15)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum15-5cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 15)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum15-5cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 15)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c5)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 5)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 1, 2, 3, 4 y 6 para celdas con restriccion 16 y
;;; numero de casillas 5
(defrule bloque-magico-sum16-5cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 6)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum16-5cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 6)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum16-5cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 6)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum16-5cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 6)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum16-5cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c5)) (rango $?ini ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 6)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 4, 6, 7, 8 y 9 para celdas con restriccion 34 y
;;; numero de casillas 5
(defrule bloque-magico-sum34-5cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 34)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 4) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum34-5cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 34)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 4) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum34-5cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 34)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 4) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum34-5cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 34)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 4) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum34-5cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 34)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c5)) (rango $?ini ?r&:(and (neq ?r 4) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Elimina valor distintos de 5, 6, 7, 8 y 9 para celdas con restriccion 35 y
;;; numero de casillas 5
(defrule bloque-magico-sum35-5cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 35)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c1)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum35-5cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 35)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c2)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum35-5cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 35)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c3)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum35-5cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 35)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c4)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum35-5cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 35)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?i&:(eq ?i ?c5)) (rango $?ini ?r&:(and (neq ?r 5) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 7, 8 o 9 para celdas con restriccion 21 y numero de casillas 6
(defrule bloque-magico-sum21-6cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 21)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum21-6cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 21)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum21-6cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 21)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum21-6cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 21)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum21-6cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 21)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum21-6cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 21)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 6, 8 o 9 para celdas con restriccion 22 y numero de casillas 6
(defrule bloque-magico-sum22-6cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 22)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 6) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum22-6cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 22)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 6) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum22-6cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 22)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 6) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum22-6cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 22)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 6) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum22-6cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 22)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 6) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum22-6cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 22)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 6) (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 1, 2 o 4 para celdas con restriccion 38 y numero de casillas 6
(defrule bloque-magico-sum38-6cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-6cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-6cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-6cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-6cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-6cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 4)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 1, 2 o 3 para celdas con restriccion 39 y numero de casillas 6
(defrule bloque-magico-sum39-6cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-6cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-6cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-6cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-6cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-6cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 8 o 9 para celdas con restriccion 28 y numero de casillas 7
(defrule bloque-magico-sum28-7cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum28-7cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum28-7cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum28-7cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum28-7cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum28-7cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum28-7cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(or (eq ?r 8) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)


;;; BM - Eliminar valor 7 o 9 para celdas con restriccion 29 y numero de casillas 7
(defrule bloque-magico-sum29-7cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-7cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-7cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-7cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-7cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-7cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum29-7cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(or (eq ?r 7) (eq ?r 9)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 1 o 3 para celdas con restriccion 41 y numero de casillas 7
(defrule bloque-magico-sum41-7cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-7cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-7cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-7cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-7cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-7cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-7cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 3)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 1 o 2 para celdas con restriccion 42 y numero de casillas 7
(defrule bloque-magico-sum42-7cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-7cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-7cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-7cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-7cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-7cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-7cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(or (eq ?r 1) (eq ?r 2)) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 9 para celdas con restriccion 36 y numero de casillas 8
(defrule bloque-magico-sum36-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum36-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum36-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum36-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum36-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum36-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum36-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum36-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 9) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 8 para celdas con restriccion 37 y numero de casillas 8
(defrule bloque-magico-sum37-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum37-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum37-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum37-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum37-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum37-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum37-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum37-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 8) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 7 para celdas con restriccion 38 y numero de casillas 8
(defrule bloque-magico-sum38-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum38-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 7) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 6 para celdas con restriccion 39 y numero de casillas 8
(defrule bloque-magico-sum39-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum39-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 6) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 5 para celdas con restriccion 40 y numero de casillas 8
(defrule bloque-magico-sum40-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum40-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum40-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum40-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum40-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum40-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum40-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum40-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 40)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 5) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 4 para celdas con restriccion 41 y numero de casillas 8
(defrule bloque-magico-sum41-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum41-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 4) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 3 para celdas con restriccion 42 y numero de casillas 8
(defrule bloque-magico-sum42-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum42-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 3) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 2 para celdas con restriccion 43 y numero de casillas 8
(defrule bloque-magico-sum43-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum43-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum43-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum43-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum43-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum43-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum43-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum43-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 2) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

;;; BM - Eliminar valor 1 para celdas con restriccion 44 y numero de casillas 8
(defrule bloque-magico-sum44-8cas-elimina-de-c1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c1)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum44-8cas-elimina-de-c2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c2)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum44-8cas-elimina-de-c3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c3)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum44-8cas-elimina-de-c4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c4)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum44-8cas-elimina-de-c5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c5)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum44-8cas-elimina-de-c6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c6)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum44-8cas-elimina-de-c7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c7)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

(defrule bloque-magico-sum44-8cas-elimina-de-c8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?i&:(eq  ?i ?c8)) (rango $?ini ?r&:(eq ?r 1) $?fin))
  (test (or (> (length $?ini) 0)(> (length $?fin) 0)))
  =>
  (modify ?h2
          (rango $?ini $?fin))
)

