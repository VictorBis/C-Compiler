#lang nanopass

(require nanopass/base)
(require racket/set)
(require racket/fixnum)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr and or not)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

(define (type? x) (memq x '(Bool Char Int List String Lambda)))

;; LENGUAJES

;Lenguaje Fuente
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
    c
    l
    s
    pr
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* e)
    (e0 e1 ...)))

;Lenguaje en el que se sustituye las multiples expresiones en el cuerpo de
;lambda, let y letrec por una única expresión begin
(define-language L0
  (extends LF)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body* ... body)
           (let ([x* t* e*] ...) body* ... body)
           (letrec ([x* t* e*] ...) body* ... body))
        (+ (lambda ([x* t*] ...) body)
           (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body)
           (or e* ...)
           (and e* ...)
           (not e))))

;;Se definen las primitivas sin operaciones logicas
(define (primitive-no-logic? x) (memq x '(+ - * / length car cdr)))

(define primitive-no-logic '(+ - * / length car cdr))
;;Lenguaje que elimina las operaciones logicas y las sustituye por expresiones if
(define-language L4
  (extends L0)
  (terminals
   (- (primitive (pr)))
   (+ (primitive-no-logic(pr))))
  (Expr (e body)
        (- (or e* ...)
           (and e* ...)
           (not e))))

;;Lenguaje para añadir una lambda cada que se encuentre una primitiva
(define-language L5
    (extends L4)
    (Expr (e body)
      (- pr)
      (+ (primapp pr e* ...))))

;;Lenguaje para eliminar constantes y reemplazarlos con quote constantes
;;Se elimina el constructor para constantes y se agrega uno nuevo 'cuote'
(define-language L6
    (extends L5)
    (Expr (e body)
      (- c)
      (+ (cuote c))))

;; PARSERS

(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)

;; PROCESOS

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : LF (ir) -> L0 ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))

;Funcion auxiliar que convierte un and a un if
;Recibe 2 paramteros c1 y c2
;c1 -> Clausula 1
;c2 -> Clausula 2
;Se llama recursvamente en caso de que se tengan mas de 2 clausulas
(define (and-to-if c1 c2)
            (let f ([c1 c1] [c2 c2])
           (if (null? c2)
               c1
               `(if , c1 , (f (car c2)(cdr c2)) #f))))

;Funcion auxiliar que convierte un or a un if
;Recibe 2 paramteros c1 y c2
;c1 -> Clausula 1
;c2 -> Clausula 2
;Se llama recursvamente en caso de que se tengan mas de 2 clausulas
(define (or-to-if c1 c2)
          (let f ([c1 c1] [c2 c2])
           (if (null? c2)
               c1
               `(if,c1,c1,(f (car c2) (cdr c2))))))

;Proceso que cambia las expresiones logicas por expresiones if
;(and) => t [Racket devuelve #t al introducir and sin clausulas]
;(or) => f [Racket devuelve #f al introducir or sin clausulas]
(define-pass remove-logical-operators : L0 (ir) -> L4 ()
  (Expr : Expr (ir) -> Expr ()
        [(not ,[e0]) `(if ,e0 #f #t)]
        [(and) #t]
        [(or) #f]
        [(and,[e],[e*] ...)
         (and-to-if e e*)]
        [(or,[e],[e*] ...)
         (or-to-if e e*)]))

;Proceso que elimina las primitivas como expresiones y las cambia por lambdas o primapp
(define-pass eta-expand : L4 (ir) -> L5 ()
  (Expr : Expr (ir) -> Expr ()
    [(,pr,[e*] ...)
     (if (memq pr '(+ - * /))
         `((lambda ([x Int] [y Int]) (primapp ,pr x y)) ,e*)
         (if (memq pr '(length car cdr))
             `((lambda ([x List]) (primapp ,pr x)) ,e*)
              (error 'error "Invalid primitive")))]))

;Proceso para quotear las contantes
(define-pass quote-const : L5 (ir) -> L6 ()
    (Expr : Expr (ir) -> Expr ()
      [,c `(cuote,c)]))

;Proceso encargado de verificar que las expresiones letrec asignen únicamente
;expresiones lambda a variables
(define-pass purify-recursion : L6 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr ()
        [(letrec ([,x* ,t* ,e*] ...) ,body)
         (let f ([x* x*][t* t*] [e* e*])
           (if (null? t*)
               body
               (if (equal? 'Lambda (car t*))
                   `(letrec ([,(car x*) ,(car t*) ,(car e*)]) ,(f (cdr x*) (cdr t*) (cdr e*)))
                   `((let ([,(car x*) ,(car t*) ,(car e*)])),(f (cdr x*) (cdr t*) (cdr e*))))))]))

;;Proceso para traducir una aplicacion de una funcion a una expresion let
(define-pass direct-app : L6 (ir) -> L6 ()
    (Expr : Expr (ir) -> Expr ()
      [((lambda ([,x* ,t*] ...) ,e0) ,e* ...)
       `(let ([,x* ,t*,e*] ...) ,e0)]))
