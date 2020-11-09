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
;;Verifica si es un tipo basico
(define (b-type? x) (memq x '(Bool Char Int List String Lambda)))
;; Verifica si es un tipo compuesto
(define (c-type? x) (if (list? x) 
	(let* (
		[f (car x)]
		[s (cadr x)]
		[t (caddr x)])
	(or (and (equal? f 'List) (equal? s 'of) (type? t)) 
		(and (type? f) (equal? s '→) (type? t))))
	#f))

;; Verifica si es una primitiva aritmtica
(define (arit? x) (memq x '(+ - * /)))

;; Verifica si es una primitiva de listas
(define (lst? x) (memq x '(length car cdr)))

;; LENGUAJES

;; Lenguaje de entrada para la práctica
(define-language L8
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    (quot c)
    (begin e* ... e)
    (primapp pr e* ...)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)
    (let ([x t e]) body)
    (letrec ([x t e]) body)
    (letfun ([x t e]) body)
    (list e* ...)
    (e0 e1 ...)))

;; Lenguaje L9
;; La funcion Lambda es cambiada para que reciba un unico parametro
(define-language L9
  (extends L8)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body))
        (+ (lambda ([x t]) body))))

;; Lenguaje 10
;; Se agrega el constructor const y se elimina el constructor quot
(define-language L10
  (extends L9)
  (Expr (e body)
        (- (quot c))
        (+ (const t c))))

;; PARSERS 
(define-parser parser-L8 L8)
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)

;;PROCESOS

;;Funcion curry
;;Proceso encargado de currificar las expresiones lambda
(define-pass curry : L8 (ir) -> L9 ()
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x* ,t*] ...) ,[body])
        (let f ([x* x*] [t* t*])
          (if (not(null? x*))
              `(lambda ([,(car x*) ,(car t*)]) ,(f (cdr x*) (cdr t*)))
              body
              ))]))

;;Funcion type-const
;;Proceso encargado de colocar anotaciones de tipos correspondientes a las constantes
(define-pass type-const : L9 (ir) -> L10 ()
  (Expr : Expr (ir) -> Expr ()
        [(quot ,c)
         (if (integer? c)
             `(const Int ,c)
              (if (boolean? c)
                 `(const Bool ,c)
                  (if (char? c)
                     `(const Char ,c)
                      (error "Consatnte inválida"))))]))

;; Función que verifica si dos tipos son unificables, para mas detalle consultar 
;; la especificación.
(define (unify t1 t2)
	(if (and (type? t1) (type? t2))
		(cond 
			[(equal? t1 t2) #t]
			[(and (equal? 'List t1) (list? t2)) (equal? (car t2) 'List)]
			[(and (equal? 'List t2) (list? t1)) (equal? (car t1) 'List)]
			[(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)) (unify (caddr t1) (caddr t2)))]
			[else #f])
		(error "Se esperaban 2 tipos")))

;; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
	(if (equal? (car lst) 'List)
		(part (cdr lst))
		(car lst)))

;; Funcion que busca un símbolo en la lista y regresa su tipo
(define lookup
  (lambda (symbol env)
    (if(symbol? symbol)
       (let recursiveLookup([symbol symbol] [env env])
         (if(equal? symbol (car (car env)))
            (cdr (car env))
            (if(null? (cdr env))
               (error "El símblolo no pertence al contexto")
               (recursiveLookup symbol (cdr env)))))                 
       (error "No es un símbolo"))))

;;Funcion J
(define (J expr ctx)
  (nanopass-case (L10 Expr) expr
    [,x (lookup x ctx)]
    [(const ,t ,c) t]
    [(list) 'List]
    [(begin ,e* ... ,e) (J `,e ctx)]
    [(primapp ,pr ,[e*] ...)
     (if (or (arit? pr) (equal? pr 'length))
         'Int
         (if (equal? pr 'car)
             (last (last e*))
             (if (equal? pr 'cdr)
                 e*
                 (error "Operador inválido"))))]
    [(if ,e0 ,e1 ,e2)
     (if (unify (J `,e1 ctx) (J `,e2 ctx))
         (J `,e1 ctx)
          (error "Los tipos no son unificables"))]
    [(lambda ([,x ,t]) ,body) (let ([nctx (set-add ctx (cons x t))]) `(,t → ,(J `,body nctx)))]
    [(let ([,x ,t ,e]) ,body)
     (if (unify (J `,e ctx) (let ([nctx (set-add ctx (cons x t))]) (J `,body nctx)))
         (let ([nctx (set-add ctx (cons x t))]) (J `,body nctx))
         (error "Los tipos no son unificables"))]
    [(letrec ([,x ,t ,e]) ,body)
     (if (unify (let ([nctx (set-add ctx (cons x t))]) (J `,e nctx)) (let ([nctx (set-add ctx (cons x t))]) (J `,body nctx)))
         (let ([nctx (set-add ctx (cons x t))]) (J `,body nctx))
         (error "Los tipos no son unificables"))]
    [(letfun ([,x ,t ,e]) ,body)
     (if (unify (J `,e ctx) t)
         (let ([nctx (set-add ctx (cons x t))]) (J `,body nctx))
         (error "Los tipos no son unificables"))]
    [(list ,[e*] ... )
     (let f ([e e*])
       (if (null? e)
          `(List of ,(part e*))
           (if (unify (car e) (part e*))
               (f (cdr e))
               (error "Listas Homogeneas"))))]
    [(,e0 ,e1 ...)
     (if (unify (J `,e0 ctx) (J `,e1 ctx))
         (J `,e1 ctx)
         (error "Los tipos no son unificables"))]
    [else "Expr incorrecta"]))

;;Funcion ecargada de quitar el tipo Lambda y sustituirla por el
;;tipo que corresponda a la definición de la función
(define-pass type-infer : L10 (ir) -> L10()
  (Expr : Expr(ir) -> Expr()
        [(let ([,x ,t ,e]) ,body)
         (if (equal? t 'List)
             `(letrec ([,x ,(J `,e '()) ,e]) ,body)
             `(letrec ([,x ,t ,e] ,body)))]
        [(letrec ([,x ,t ,e]) ,body)
         (if (or (equal? t 'Lambda) (equal? t 'List))
             `(letrec ([,x ,(J `,e '()) ,e]) ,body)
             `(letrec ([,x ,t ,e] ,body)))]
        [(letfun ([,x ,t ,e]) ,body)
         (if (or (equal? t 'Lambda) (equal? t 'List))
             `(letfun ([,x ,(J `,e '()) ,e]) ,body)
             `(letfun ([,x ,t ,e] ,body)))]))
;; PRUEBAS PARA LA FUNCIÓN J				
(J (parser-L10 'x) `( ,(cons 'x 'Int)))
;;Salida : 'Int
(J (parser-L10 '(const Int 5)) '())
;; Salida : 'Int
(J (parser-L10 '(begin x x x (const Int 5) x x x x (const Bool #t))) `( ,(cons 'x 'Int)))
;; Salida : 'Bool
(J (parser-L10 '(primapp + (const Bool 6) (const Int 5))) '())
;; Salida : 'Int
(J (parser-L10 '(primapp cdr (list (const Int 6) (const Int 5)))) '())
;; Salida : '(List of Int)
(J (parser-L10 '(primapp car (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
(J (parser-L10 '(primapp length (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
(J (parser-L10 '(if (const Bool #t) x (const Int 5))) `( ,(cons 'x 'Int)))
;; Salida : 'Int
(J (parser-L10 '(lambda ([x Int]) x)) '())
;; Salida : '(Int → Int)
(J (parser-L10 '(let ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
(J (parser-L10 '(letrec ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
(J (parser-L10 '(list)) '())
;; Salida : 'List
(J (parser-L10 '(list (const Bool #t) (const Bool #f))) '())
;; Salida : '(List of Bool)
(J (parser-L10 '(list (list) (list (const Bool #f) (const Bool #t)))) '())
;; Salida : '(List of (List of Bool))
;; CASOS DE ERROR
;(J (parser-L10 '(list (const Int 5) (const Bool #f))) '())
;; Salida : error : Listas homogeneas
;(J (parser-L10 '(list (list) (list (list (const Bool #t) (const Bool #f))) (list (list (const Int 5) (const Int 6))))) '())
;; Salida : error : Listas homogeneas


;;EJEMPLOS
;(unparse-L9 (curry (parser-L8 '(lambda ([x Int] [y Int]) (primapp + x y)))))
;(unparse-L10 (type-const (parser-L9 '(quot #\A))))
;(unparse-L10 (type-infer (parser-L10 '(letrec ([foo Lambda (lambda ([x Int]) x)]) (foo (const Int 5))))))