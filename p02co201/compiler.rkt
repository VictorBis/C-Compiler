#lang nanopass

(require nanopass/base)

;; Definición del Lenguaje Fuente
(define-language LF
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (string (s))
   (type (t)))
  (Expr (e body)
    x
    pr
    c
    l
    s
    t
    (pr c* ... c)
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (e0 e1 ...)))

;; Definición del predicado que verifica las variables
(define (variable? x)
  (symbol? x))

;; Se definen los primitivos del lenguaje
(define primitives '(+ - * / and or lenght car cdr))

;; Definición del predicado que verifica las primitivas
(define (primitive? pr)
  (and (memq pr primitives) #t))

;; Definición del predicado que verifica las constantes
(define (constant? c)
  (or (integer? c)
      (boolean? c)
      (char? c)))

;; Se definen los primitivos del lenguaje
(define types '(Bool Int Char List String))

;; Definición del predicado que verifica los tipos
(define (type? t)
  (and (memq t types) #t))

;; Proceso del compilador encargado de hacer explicitas las expresiones
;; begin en el cuerpo de lambda, let y letrec
(define-pass make-explicit : LF (ir) -> LF ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* , t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x*, t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* , t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t*, e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* , t*,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* , t*, e*] ...) (begin ,body* ... ,body))]))

;; Lenguaje 1: Se elimina el if sin el caso del else y se agrega void a los primitivos
(define-language L1
  (extends LF)
  (terminals
    (- (primitive (pr)))
    (+ (primitive+void (pr))))
  (Expr (e body)
    (- (if e0 e1))))

;; Definimos los primitivos agregando void como terminal
(define primitives+void (append '(void) primitives))

;; Definimos el predicado que verifica los nuevos primitivos
(define (primitive+void? pr)
  (and (memq pr primitives+void) #t))

;; Proceso del compilador encargado de eliminar el if sin el caso del else
(define-pass remove-one-armed-if : LF (e) -> L1 ()
  (Expr : Expr (e) -> Expr ()
        [(if, [e0], [e1])
         `(if, e0, e1 (void))]))

;; Lenguaje 2: Se elimina string de los primitivos
;;(define-language L2
;;  (extends L1)
;;  (terminals
;;   (- (string(s)))))
(define-language L2
  (extends L1)
  (terminals
    (- (string (s))))
  (Expr (e body)
    (- s)))
;; Proceso del compilador encargado de pasar los string a listas
(define-pass remove-string : L1 (e) -> L2 ()
  (Expr : Expr (e) -> Expr ()
        [,s (string->list s)]))

;; Función parser del lenguaje LF
(define-parser parser-LF LF)

;; Función parser del lenguaje L1
(define-parser parser-L1 L1)

(unparse-L1 (remove-one-armed-if (parser-LF '(if 1 2))))
(unparse-L2 (remove-string (parser-L1 "Hola")))