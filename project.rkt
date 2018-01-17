;; PL Project - Fall 2017
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; Add the missing ones

(struct var  (s)                    #:transparent)  ;; variable
(struct int  (num)                  #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)                #:transparent)  ;; add two expressions
(struct mult (e1 e2)                #:transparent)  ;; multiply two expressions
(struct neg  (e1)                   #:transparent)  ;; negate an
(struct fun  (nameopt formal body)  #:transparent)  ;; a recursive(?) 1-argument function
(struct islthan (e1 e2)             #:transparent)  ;; compare two expressions
(struct ifzero (e1 e2 e3)           #:transparent)  ;; decide on e1 if it is zero then e2 evaluates else e3 will be evaluated
(struct ifgthan (e1 e2 e3 e4)       #:transparent)  ;; result is e3 if is e1 strictly greater than e2 else the result is e4
(struct call (funexp actual)        #:transparent)  ;; function call
(struct mlet (s e1 e2)              #:transparent)  ;; value of s is bound to e1 in e2
(struct apair (e1 e2)               #:transparent)  ;; pair constructor
(struct first (e1)                  #:transparent)  ;; first part of pair
(struct second (e1)                 #:transparent)  ;; second part of pair
(struct munit   ()                  #:transparent)  ;; unit value -- good for ending a list
(struct ismunit (e)                 #:transparent)  ;; if e1 is unit then 1 else 0
(struct closure (env fun)           #:transparent)  ;; a closure is not in "source" programs; it is what functions evaluate to

;; Problem 1
(define (racketlist->numexlist xs)
(cond
  [(not (list? xs)) ( error "Can't convert non list racket type to a NUMEX list")]
  [(null? xs) (munit)]
  [#t (apair  (car xs) (racketlist->numexlist (cdr xs)))]
  ))

(define (numexlist->racketlist xs)
  (cond
  [(munit? xs) '()]
  [(not (apair? xs)) (error "Can't convert non NUMEX list to racket type")]
  [#t (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]
  ))

;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(not (string? str)) (error "Can't search on environment with a non string name")]
        [(null? env) (error "Unbound variable during evaluation" str)]
        [(not(list? env)) (error "Environment is not a list")]
        [(not(pair? (car env))) (error "Environment list member is not a pair")]
        [(equal? (car (car env)) str) (cdr (car env))]
        [#t (envlookup (cdr env) str)]))
;;
;;change environment add or modify variable with name str to value 
;;
(define (envChanger env str expression)
   (cond[(not (string? str)) (error "Can't create temporary  environment with a non string name")]
        [(not(list? env)) (error "Input environment is not a list")]
        [(null? env) (cons (cons str expression) null)]
        [(not(pair? (car env))) (error "Input environment list member is not a pair")]
        [(equal? (car (car env)) str) (envChanger (cdr env) str expression)]
        [#t (cons (car env)(envChanger (cdr env) str expression))]))
;;
;;detect that input is a numex value
;;
(define (NUMEX-value? input)
  (or (closure? input)(munit? input)(apair? input)(int? input)))
;;
;;detect that input is a numex expression
;;
(define (NUMEX-exp? input)
  (or (var? input)(int? input)(add? input)(mult? input)
      (neg? input)(fun? input)(islthan? input)(ifzero? input)
      (ifgthan? input)(call? input)(mlet? input)(apair? input)
      (first? input)(second? input)(munit? input)(ismunit? input)
      (closure? input)))
;;
;;detect that input is an env
;;
(define (env? input)
  (cond[(not (list? input)) #f]
       [(null? input) #t]
       [(not (pair? (car input))) #f]
       [(not (string? (car (car input)))) #f ]
       [(not (NUMEX-value? (cdr (car input)))) #f]
       [#t (env? (cdr input))]
       ))
;; Do NOT change the two cases given to you.
;; DO add more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e)(envlookup env (var-s e))]
        [(int? e)(if (integer? (int-num e))
            e
            (error "Can't convert a Racket non integer to a NUMEX int"))]
        [(add? e)
         (let ([v1 (eval-under-env (add-e1 e) env)]
               [v2 (eval-under-env (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1)
                       (int-num v2)))
               (error "NUMEX addition applied to non-number")))]
        [(mult? e)
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (* (int-num v1)
                       (int-num v2)))
               (error "NUMEX multiplication applied to non-number")))]
        [(neg? e)
         (let ([v (eval-under-env (neg-e1 e) env)])
           (if (int? v) (int (- (int-num v))) 
               (error "NUMEX negation on non integer expression" v)))]
        [(islthan? e)
         (let ([v1 (eval-under-env (islthan-e1 e) env)]
               [v2 (eval-under-env (islthan-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (if(< (int-num v1)(int-num v2))(int 1)(int 0))
               (error "NUMEX islthan doesn't work on gaurd with non integer values")))]
        [(ifzero? e)
         (let ([v (eval-under-env (ifzero-e1 e) env)])
           (if (int? v)
                (if (= (int-num v) 0 ) (eval-under-env (ifzero-e2 e) env)(eval-under-env (ifzero-e3 e) env))
                (error "NUMEX ifzero doesn't work on gaurd with  non integer value")))]
        [(ifgthan? e)
         (let ([v1 (eval-under-env (ifgthan-e1 e) env)]
               [v2 (eval-under-env (ifgthan-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (if(> (int-num v1)(int-num v2))(eval-under-env (ifgthan-e3 e) env)(eval-under-env (ifgthan-e4 e) env))
               (error "NUMEX isgthan doesn't work on gaurds with non integer values")))]
        [(mlet? e)
         (let ([v1 (eval-under-env (mlet-e1 e) env)])
           (cond
             [(not(string? (mlet-s e)))(error "NUMEX mlet doesn't work with non string names")]
             [#t (eval-under-env (mlet-e2 e) (envChanger env (mlet-s e) v1))]
             ))]
        [(apair? e)
         (let ([v1 (eval-under-env (apair-e1 e) env)]
               [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))]
        [(first? e)
         (let ([v (eval-under-env (first-e1 e) env)])
           (if(apair? v)
              (apair-e1 v)
              (error "NUMEX Can't get first element of non apair")))]
         [(second? e)
          (let ([v (eval-under-env (second-e1 e) env)])
           (if(apair? v)
              (apair-e2 v)
              (error "NUMEX Can't get second element of non apair")))]
         [(munit? e) e]
         [(ismunit? e)
           (let ([v (eval-under-env (ismunit-e e) env)])
             (if (munit? v)(int 1)(int 0)))]
         [(closure? e)
          (cond[(not (env? (closure-env e)))(error "Numex Closure only works on valid environment")]
               [(not (fun? (closure-fun e)))(error "Numex Closure need a valid function")]
               [#t (closure (closure-env e)(closure-fun e))])]
         [(fun? e)
          (cond[(not (or(null? (fun-nameopt e))(string? (fun-nameopt e))))(error "Numex function name should be string or null")]
               [(not (string?  (fun-formal e)))(error "Numex argument should be a string")]
               [#t (closure env e)])]
         [(call? e)
          (let ([v1 (eval-under-env (call-funexp e) env)]
                [v2 (eval-under-env (call-actual e) env)])
            (if(and (closure? v1) (NUMEX-value? v2)) 
               (let([tempEnv (envChanger (closure-env v1) (fun-formal (closure-fun v1)) v2)])
                 (if (null?(fun-nameopt (closure-fun v1)))
                     (eval-under-env (fun-body (closure-fun v1)) tempEnv)
                     (eval-under-env (fun-body (closure-fun v1)) (envChanger tempEnv (fun-nameopt (closure-fun v1)) v1))))
               (error "Function call should have a closure and value")))]
        ;; CHANGE add more cases here
        [#t (error (format "bad NUMEX expression: ~v" e))]))


;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))

(define env (list (cons "first" (int 1)) (cons "second" (int 2)) (cons "third" (apair (add (int 2)(int 5))(int 3))))) 

;; Problem 3

(define (ifmunit e1 e2 e3)
  (if (and(NUMEX-exp? e1)(NUMEX-exp? e2)(NUMEX-exp? e3))
  (ifzero (add (int -1) (ismunit e1)) e2 e3)
  (error "NUMEX ifmunit macro need all input be NUMEX expression")
  ))

(define (mlet* bs e2)
  (cond
    [(not(list? bs))(error "NUMEX mlet* macro need a list input")]
    [(not (NUMEX-exp? e2))(error "NUMEX mlet* macro need NUMEX expression as second input")]
    [(null? bs) e2]
    [(not (pair? (car bs)))(error "NUMEX mlet* macro need a list of PAIRS input")]
    [(not (string? (car (car bs)))) (error "NUMEX mlet* macro input list of pair should have a string head")]
    [(not (NUMEX-exp? (cdr (car bs))))(error "NUMEX mlet* macro input list of pair should have a NUMEX expression tail")]
    [#t (mlet (car (car bs)) (cdr (car bs)) (mlet* (cdr bs) e2))]
    ))

(define (ifeq e1 e2 e3 e4)
  (cond
    [(not (and (NUMEX-exp? e1)(NUMEX-exp? e2)(NUMEX-exp? e3)(NUMEX-exp? e4)))(error "NUMEX ifeq macro inputs should all be NUMEX expression")]
    [#t (ifzero (add (neg e1) e2) e3 e4)]
    ))
#|
;; Problem 4

(define numex-map "CHANGE")

(define numex-mapAddN
  (mlet "map" numex-map
        "CHANGE (notice map is now in NUMEX scope)"))

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))
|#