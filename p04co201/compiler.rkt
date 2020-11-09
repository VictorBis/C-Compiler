#lang nanopass

(require nanopass/base)
(require racket/set)

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
    t
    pr
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* ...)
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
           (letrec ([x* t* e*] ...) body))))

;Lenguaje Resultante de la práctica 3
(define-language L6
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    t
    (quot c)
    (begin e* ... e)
    (primapp pr e* ...)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)
    (let ([x* t* e*] ...) body)
    (letrec ([x* t* e*] ...) body)
    (list e* ...)
    (e0 e1 ...)))

;Lenguaje en el que se modifican los constructores let y letrec para
;que tengan una sola asignación
(define-language L7
  (extends L6)
  (Expr (e body)
        (- (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body))
        (+ (let ([x t e]) body)
           (letrec ([x t e]) body))))

;Lenguaje en el que se agrega el constructor letfun
(define-language L8
  (extends L7)
  (Expre (e body)
         (+ (letfun ([x t e]) body))))

;; PARSERS
(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)

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

;Proceso encargado de currificar las expresiones let y letrec
(define-pass curry-let : L6 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x* ,t* ,[e*]] ...) ,[body])
        (let f ([x* x*] [t* t*] [e* e*])
          (if (not(null? x*))
              `(let ([,(car x*) ,(car t*) ,(car e*)]) ,(f (cdr x*) (cdr t*) (cdr e*)))
              body
              ))]
         [(letrec ([,x* ,t* ,[e*]] ...) ,[body])
        (let f ([x* x*] [t* t*] [e* e*])
          (if (not(null? x*))
              `(letrec ([,(car x*) ,(car t*) ,(car e*)]) ,(f (cdr x*) (cdr t*) (cdr e*)))
              body
              ))]))

;Proceso en el que se detectan los let utilizados para definir funciones y se reemplazan por letrec
(define-pass identify-assigments : L7 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,body)
         (if (equal? t 'Lambda)
         `(letrec ([,x Lambda ,e]) ,body)
         `(let ([,x ,t ,e]) ,body))]))

;Funcion para generar variables unicas
(define unique-vars
            (let ()
              (define count 0)
              (lambda (name)
                (let ([c count])
                  (set! count (+ count 1))
                  (string->symbol
                   (string-append (symbol->string name) (number->string c)))))))

;Proceso para asignarles un identificador a las funciones anónimas
(define-pass un-anonymous : L7 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t] ...) ,body)
         (let ([name (unique-vars 'foo)])
         `(letfun ([,name Lambda (lambda ([,x ,t] ...) ,body)]) ,name))]))

;;VERIFICADORES

;Proceso que verifica la aridad de las primitivas
(define-pass verify-arity : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [(primapp ,pr ,[e*]...)
         (let ([e e*])
           (if (memq pr '(+ - * /))
               (if (= 2 (length e))
                   `(primapp ,pr ,e* ...)
                   (error 'error "Arity mismatch"))
            (if (memq pr '(length car cdr not))
               (if (= 1 (length e))
                   `(primapp ,pr ,e* ...)
                   (error 'error "Arity mismatch"))
             (if (memq pr '(and or))
               (if (or (= 1 (length e)) (= 2 (length e)))
                   `(primapp ,pr ,e* ...)
                   (error 'error "Arity mismatch"))
             (error 'error "Invalid primitive")))))]))

;Proceso que verifica que no haya variables libres en las expresiones
;Solo se verifican las expresiones únicas, es decir, si no tienen lambdas,
;let, letrec dentro del body
(define-pass verify-vars : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [(primapp ,pr ,[e*]...)
         (let f ([e e*])
           (if (null? e)
               `(primapp ,pr ,e* ...)
               (if (variable? (car e))
                   (error 'error "There's a free var")
                   (f (cdr e)))))]
        [(let ([,x ,t ,e]) ,[body])
         (if (variable? body)
             (if (equal? x body)
                 `(let ([,x ,t ,e]) ,body)
                 (error 'error "There's a free var"))
             `(let ([,x ,t ,e]) ,body))]
        [(letrec ([,x ,t ,e]) ,[body])
         (if (variable? body)
             (if (equal? x body)
                 `(letrec ([,x ,t ,e]) ,body)
                 (error 'error "There's a free var"))
             `(letrec ([,x ,t ,e]) ,body))]
        [(if ,e0 ,e1 ,e2)
         (if (or (variable? e0) (or (variable? e1) (variable? e2)))
         (error 'error "There's a free var")
         `(if ,e0 ,e1 ,e2))]
        [(lambda ([,x* ,t*] ...) ,[body])
         (let f ([x x*] [body body])
           (if (null? x)
               (error 'error "There's a free var")
               (if (variable? body)
                   (if (equal? (car x) body)
                       `(lambda ([,x* ,t*] ...) ,body)
                       (f (cdr x) body))
               `(lambda ([,x* ,t*] ...) ,body))))]
        [(list ,[e*] ... ,e)
         (if (variable? e)
             (error 'error "There's a free var")
             (let f ([e* e*])
               (if (null? e*)
                   `(list ,e* ... ,e)
                   (if (variable? e*)
                       (error 'error "There's a free var")
                       (f (cdr e*))))))]
        [(begin ,[e*] ... ,e)
         (if (variable? e)
             (error 'error "There's a free var")
             (let f ([e* e*])
               (if (null? e*)
                   `(begin ,e* ... ,e)
                   (if (variable? e*)
                       (error 'error "There's a free var")
                       (f (cdr e*))))))]))


;;EJEMPLOS
;(unparse-L7 (curry-let (parser-L6 '(let ([x Int (quot 4)] [y Int (quot 6)]) (primapp + x y)))))
;(unparse-L7 (identify-assigments (parser-L7 '(let ([foo Lambda (lambda ([x Int]) x)]) (foo (quot 5))))))
;(unparse-L8 (un-anonymous (parser-L7 '(lambda ([x Int]) x))))
;(unparse-L8 (verify-arity (parser-L8 '(primapp * (quot 3) (quot 4)))))