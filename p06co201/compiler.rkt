#lang nanopass

(define fun-count 0)

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

;; SISTEMA DE TIPOS
;; Int | Char | Bool | Lambda | List | (List of T) | (T → T)
(define (type? x) (or (b-type? x) (c-type? x)))
(define (b-type? x) (memq x '(Bool Char Int List String Lambda)))
(define (c-type? x) (if (list? x) 
	(let* (
		[f (car x)]
		[s (cadr x)]
		[t (caddr x)])
	(or (and (equal? f 'List) (equal? s 'of) (type? t)) 
		(and (type? f) (equal? s '→) (type? t))))
	#f))

(define (arit? x) (memq x '(+ - * /)))

(define (lst? x) (memq x '(length car cdr)))

;;LENGUAJES
(define-language L10
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    (const t c)
    (begin e* ... e)
    (primapp pr e* ...)
    (if e0 e1 e2)
    (lambda ([x t]) body)
    (let ([x t e]) body)
    (letrec ([x t e]) body)
    (letfun ([x t e]) body)
    (list e* ...)
    (e0 e1)))

;;Lenguaje L11
;;Se convierte al constructor lambda en multiparamétrico
(define-language L11
  (extends L10)
  (Expr (e body)
        (- (lambda ([x t])body))
        (+ (lambda ([x* t*]...)body))))

;;Lenguaje 12
;;Los constructores de asignación solo reciben una variable
(define-language L12
  (extends L11)
  (Expr (e body)
        (- (let ([x t e]) body)
           (letrec ([x t e]) body)
           (letfun ([x t e]) body))
        (+ (let body)
           (letrec body)
           (letfun body))))

;;Parsers
(define-parser parser-L10 L10)
(define-parser parser-L11 L11)
(define-parser parser-L12 L12)

;;PROCESOS

(define-pass uncurry : L10 (ir) -> L11 ()
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t]) ,[body]) (body)]))

;;Función para generar la tabla de símbolos de una expresión del lenguaje
(define (symbol-table-var expr hash)
  (nanopass-case (L11 Expr) expr
                 [(begin ,e* ... ,e) (begin (map (lambda (e) (symbol-table-var e hash)) e*)
                                            (symbol-table-var e hash))]
                 [(primapp ,pr ,[e*]...,e) (begin (map (lambda (e) (symbol-table-var e hash)) e*)
                                            (symbol-table-var e hash))]
                 [(if ,e0 ,e1 ,e2) (begin (symbol-table-var e0 hash)
                                          (symbol-table-var e1 hash)
                                          (symbol-table-var e2 hash))]
  	 	[(lambda ([,x ,t]) ,body) (symbol-table-var body hash)]
                [(let ([,x ,t ,e]) ,body) (begin (hash-set*! hash x (cons t (unparse-L11 e)))
                                                 (symbol-table-var body hash))]
                [(letrec ([,x ,t ,e]) ,body) (begin (hash-set*! hash x (cons t (unparse-L11 e)))
                                                    (symbol-table-var body hash))]
                [(letfun ([,x ,t ,e]) ,body) (begin (hash-set*! hash x (cons t (unparse-L11 e)))
                                                    (symbol-table-var body hash))]
  	 	[(list ,e* ... ,e) (begin (map (lambda (e) (symbol-table-var e hash)) e*)
                                          (symbol-table-var e hash))]
                [(,e0 ,e1) (begin (symbol-table-var e0 hash)
                                  (symbol-table-var e1 hash))]
                [else hash]))

;;Proceso que modifica los constructores let, letrec y letfun eliminando el valor asociado
;;a los identificadores y el tipo correspondiente
(define-pass assigment : L11 (ir) -> L12 (hash)
  (definitions
    (define hash (make-hash)))
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,[body]) `(let ,body)]
        [(letrec ([,x ,t ,e]) ,[body])   `(letrec ,body)]
        [(letfun ([,x ,t ,e]) ,[body]) `(letfun ,body)])
	(values (Expr ir) (symbol-table-var ir hash)))

;(unparse-L11 (uncurry (parser-L10 '(lambda ([x Int]) (lambda ([y Int]) y)))))