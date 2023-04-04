#lang plai
(define eight-principles
  (list "Know your rights."
        "Acknowledge your sources."
        "Protect your work."
        "Avoid suspicion."
        "Do your own work."
        "Never falsify a record or permit another person to do so."
        "Never fabricate data, citations, or experimental results."
        "Always tell the truth when discussing your work with your instructor."))

(define-type RFAE
  [num (n number?)]
  [add (lhs RFAE?)
       (rhs RFAE?)]
  [sub (lhs RFAE?)
       (rhs RFAE?)]
  [fun (param-name symbol?)
       (body RFAE?)]
  [app (fun-expr RFAE?)
       (arg-expr RFAE?)]
  [id (name symbol?)]
  [r-struct (expressions (listof pair?))]
  [get (sub-expr RFAE?)
       (field-name symbol?)]
  [r-set (first-expr RFAE?)
         (field-name symbol?)
         (sec-expr RFAE?)]
  [seqn (first-expr RFAE?)
        (sec-expr RFAE?)])

(define-type RFAE-Value
  [numV     (n number?)]
  [closureV (param-name symbol?)
            (body RFAE?)
            (ds DefSub?)]
  [structV  (boxnum integer?)])

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value RFAE-Value?)
         (rest DefSub?)])

(define-type Store
  [mtSto]
  [aSto (address integer?)
        (name symbol?)
        (value RFAE-Value?)
        (rest Store?)])

(define-type Value*Store
  [v*s (value RFAE-Value?)
       (store Store?)])

(define (size s)
  (cond
    [(struct? s)
     (size (struct->vector s))]
    [(vector? s)
     (for/fold ([tot 0])
               ([ele (in-vector s)])
       (+ tot (size ele)))]
    [(pair? s)
     (+ 1 (size (car s)) (size (cdr s)))]
    [else 1]))

(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid BFAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp "add" 3)
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp "sub" 3)
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(fun)
            (check-pieces s-exp "fun" 3)
            (check-pieces (second s-exp) "parameter list" 1)
            (fun (first (second s-exp))
                 (parse (third s-exp)))]
           [(with) ; in lieu of a compiler
            (check-pieces s-exp "with" 3)
            (check-pieces (second s-exp) "with binding pair" 2)
            (app (fun (first (second s-exp)) (parse (third s-exp)))
                 (parse (second (second s-exp))))]
           ;new stuff
           [(struct)
            ;might have a problem here because you are only conisdering the case where there is one pair
            ;(print (first (map parse (second s-exp))))
            (r-struct (map (λ (p) (cons (first p) (parse (last p)))) (rest s-exp)))]
           [(get)
            (check-pieces s-exp "get" 3)
            (get (parse (second s-exp)) (third s-exp))]
           [(set)
            (check-pieces s-exp "r-set" 4)
            (r-set (parse (second s-exp))
                   (third s-exp)
                   (parse (fourth s-exp)))]
           [(seqn)
            (check-pieces s-exp "seqn" 3)
            (seqn (parse (second s-exp))
                  (parse (third s-exp)))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "wat")]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

;(parse '{struct {z {get {struct {z 0}} y}}})

;Stuff for storing data

; malloc : Store? -> integer?
(define (malloc st)
 (+ 1 (max-address st)))
; max-address : Store? -> integer?
(define (max-address st)
 (type-case Store st
   [mtSto () 0]
   [aSto (n v f st)
         (max n (max-address st))]))

;get helpers

(define (get_store_from_boxnum store boxnum)
  (type-case Store store
    [mtSto () (error "unknown field")]
    [aSto (address name val rest) (if (eq? boxnum address)
                                      store
                                      (get_store_from_boxnum rest boxnum))]))

(define (get_val_from_store store name)
  (type-case Store store
    [mtSto () (error "unknown field")]
    [aSto (address id val rest)
          (if (equal? name id)
              val
              (get_val_from_store rest name))]))

;set helpers

(define (store_se new_st field store)
  (type-case Store store
    [aSto (address name val rest)
          (if (equal? field name)
              (aSto address field new_st rest)
              (aSto address name val (store_se new_st field rest)))]
    [else (error "unknown field")]))

(define (store_at_add store)
  (type-case Store store
    [mtSto () 0]
    [aSto (address name val rest) address]))

;now time for interp

(define (interp a-rfae ds store)
  (type-case RFAE a-rfae
    [num (n)   (v*s (numV n) store)]
    [add (l r) (type-case Value*Store (interp l ds store)
                 [v*s (val st)
                      (type-case Value*Store (interp r ds st)
                        [v*s (val2 st2)
                             ;(print val2)(newline)
                             ;(print st2)(newline)
                             ;(print (numop + val val2 ds))
                             (v*s (numop + val val2 ds st2) st2)])])]
    [sub (l r) (type-case Value*Store (interp l ds store)
                 [v*s (val st)
                      (type-case Value*Store (interp r ds st)
                        [v*s (val2 st2)
                             ;(print val2)(newline)
                             ;(print st2)(newline)
                             ;(print (numop + val val2 ds))
                             (v*s (numop - val val2 ds st2) st2)])])]
    [id (name) (v*s (lookup name ds) store)]
    [fun (param-name body) (v*s (closureV param-name body ds) store)]
    [app (fun-expr arg-expr)
         (type-case Value*Store (interp fun-expr ds store)
           [v*s (fun-val st)
                ;(print "My fun-val is")(print fun-val)(newline)
                (type-case Value*Store (interp arg-expr ds st)
                  [v*s (arg-val arg_st)
                       ;(print "My arg-val is")(print arg-val)
                       ;(print "and you see its storage here")(print arg_st)(newline)
                       (type-case RFAE-Value fun-val
                         [closureV (param-name body closed-ds)
                                   (interp body
                                           (aSub param-name
                                                 arg-val
                                                 closed-ds)
                                           arg_st)]
                         [else (error "expected function")])])])]
    ;new stuff
    [r-struct (expressions) (if (empty? expressions)
                                (v*s (structV (store_at_add store)) store)
                            (type-case Value*Store (interp (cdr (first expressions)) ds store)
                              [v*s (val st)
                                   ;(print "R-STRUCT")(newline)
                                   ;(print "We are storing this value")(print val)(newline)
                                   (define a (malloc st))
                                   ;(print "At this index")(print a)(newline)
                                   (let ([new_st (aSto a (car (first expressions)) val st)])
                                     ;(struct-rd rest-rds ds st3)
                                     (interp (r-struct (rest expressions)) ds new_st))]))]
                                     ;(v*s val new_st))])]
    [get (sub-expr field-name) ;(print "GET")(newline)
                               (let ([val (interp sub-expr ds store)])
                                 ;(print store)
                                 ;(print "This is val")(print val)(newline)
                                 (if (Value*Store? val)
                                     (type-case Value*Store val
                                       [v*s (val1 st)
                                            (if (structV? val1)
                                                (let ([val_st (get_store_from_boxnum st (structV-boxnum val1))])
                                                  (v*s
                                                   (get_val_from_store val_st field-name)
                                                   st))
                                                (error "expected record"))])
                                 (let ([val_st (get_store_from_boxnum store (structV-boxnum val))])
                                   ;(print "GET")(newline)
                                   ;(print "We have our field-name")(print field-name)(newline)
                                   ;(print "First we evaluate the sub-expression to get the ")(print val)(newline)
                                   ;(print "Which we use to get the store of our val")(print val_st)(newline)
                                   ;(print "Which we then use to get our value")
                                   ;(print (get_val_from_store val_st field-name))(newline)
                                   ;(print store)
                                   (v*s
                                    (get_val_from_store val_st field-name)
                                    store))))]
    [r-set (first-expr field-name sec-expr)
           ;(print "SET")(newline)
           ;(print "first-expr")(print first-expr)(newline)
           ;(print "field-name")(print field-name)(newline)
           ;(print "sec-expr")(print sec-expr)(newline)
           ;(print (interp first-expr ds store))(newline)
           (if (Value*Store? (interp first-expr ds store))
               (type-case Value*Store (interp first-expr ds store)
             [v*s (val st)
                  ;(print (structV-boxnum val))(newline)
                  ;(print st)(newline)
                  ;(print (interp sec-expr ds st))(newline)
                  (type-case Value*Store (interp sec-expr ds st)
                    [v*s (val2 st2)
                         ;(print val2)
                         ;(print (store_set field-name val2 st2))(newline)
                         (if (structV? val)
                             (v*s (get_val_from_store
                                   (get_store_from_boxnum st2 (structV-boxnum val))
                                   field-name)
                                  ;(lookup-st addr named-id st3)
                                  (store_se
                                   ;(structV-boxnum val)
                                   val2 field-name st2))
                             (error "expected record"))])])
               
           (type-case Value*Store (v*s (interp first-expr ds store) store)
             [v*s (val st)
                  ;(print (structV-boxnum val))(newline)
                  ;(print st)(newline)
                  ;(print (interp sec-expr ds st))(newline)
                  (type-case Value*Store (interp sec-expr ds st)
                    [v*s (val2 st2)
                         ;(print val2)
                         ;(print (set-st (numV-n val1) field-name val2 st3))(newline)
                         (v*s (get_val_from_store
                               (get_store_from_boxnum st2 (structV-boxnum val))
                               field-name)
                              ;(lookup-st addr named-id st3)
                              (store_se
                               ;(structV-boxnum val)
                               val2 field-name st2))])]))]
    [seqn (first-expr sec-expr) (type-case Value*Store (interp first-expr ds store)
                                  [v*s (val st)
                                       (type-case Value*Store (interp sec-expr ds st)
                                         [v*s (val2 st2)
                                              ;(print "done")(newline)
                                              ;(print val1)(newline)
                                              ;(print st2)(newline)
                                              ;(print val2)(newline)
                                              ;(print st3)(newline)
                                              (v*s val2 st2)])])]))

;; numop : (number? number? -> number?) BFAE? BFAE? DefSub? -> BFAE-Value?
(define (numop op l r ds st)
  ;(define l-val (interp l ds st))
  (unless (numV? l)
    (error 'interp "expected number, got ~a" l))
  ;(define r-val (interp r ds st))
  (unless (numV? r)
    (error 'interp "expected number, got ~a" r))
  (numV (op (numV-n l) (numV-n r))))

;; lookup : symbol? DefSub? -> BFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

(define (interp-expr an-rfae)
  ;(print "THIS IS THE FINAL ANSWER")(print (interp an-rfae (mtSub) (mtSto)))(newline)
  (type-case Value*Store (interp an-rfae (mtSub) (mtSto))
    [v*s (val st) (type-case RFAE-Value val
                    [numV (n) n]
                    [structV (n) n]
                    [else (error "free identifier")])]))

;test cases for interp

;(parse '{{fun {r} {get r x}}{struct {x 1}}})
(test (interp-expr (parse '{{fun {r} {get r x}}{struct {x 1}}}))
      1)

;(parse '{{fun {r} {seqn {set r x 5}{get r x}}}{struct {x 1}}})
(test (interp-expr (parse '{{fun {r} {seqn {set r x 5}{get r x}}}{struct {x 1}}}))
      5)

;(parse '{set {struct {x 42}} x 2})
(test (interp-expr (parse '{set {struct {x 42}} x 2}))
      42)

;(parse '((fun (r) (get (get r y) z)) (struct (y (struct (z 5))))))
(test (interp-expr (parse '((fun (r) (get (get r y) z)) (struct (y (struct (z 5)))))))
      5)

;(parse `(get (struct (x 1)) x))
(test (interp-expr (parse `(get (struct (x 1)) x)))
      1)

(test (interp-expr (parse `(set (struct (x 1)) x 2)))
      1)

;(parse `(set (struct (x 42)) x 2))
(test (interp-expr (parse `(set (struct (x 42)) x 2)))
      42)

(test (interp-expr (parse `(with (b (struct (x 1))) (seqn (set b x 2) (get b x)))))
      2)

;(parse `(with (b (struct (x 1))) (+ (get b x) (seqn (set b x 2) (get b x)))))
(test (interp-expr (parse `(with (b (struct (x 1))) (+ (get b x) (seqn (set b x 2) (get b x))))))
      3)

(test (interp-expr (parse `(with (b (struct (x 1))) (+ (seqn (set b x 2) (get b x)) (get b x)))))
      4)

;(parse `(get (struct (x 1) (y 2) (z 3)) x))
(test (interp-expr (parse `(get (struct (x 1) (y 2) (z 3)) x)))
      1)

(test (interp-expr (parse `(get (struct (x 1) (y 2) (z 3)) y)))
      2)

(test (interp-expr (parse `(get (struct (x 1) (y 2) (z 3)) z)))
      3)

(test (interp-expr (parse `(set (struct (x 1) (y 2) (z 3)) x 11)))
      1)

;(parse `(get 1 x))
(test/exn (interp-expr (parse `(get 1 x)))
          "expected record")

;(parse `(set 1 x (struct (x 2))))
(test/exn (interp-expr (parse `(set 1 x (struct (x 2)))))
          "expected record")

;(parse `(get (struct (x 2)) y))
(test/exn (interp-expr (parse `(get (struct (x 2)) y)))
          "unknown field")

;(parse `(set (struct (x 2)) y 3))
(test/exn (interp-expr (parse `(set (struct (x 2)) y 3)))
          "unknown field")

(test (interp-expr (parse '((fun (r) (get (get r y) z)) (struct (y (struct (z 5)))))))
  5)

;(parse `(struct (x 1)))
(test (interp-expr (parse `(struct (x 1))))
  1)

(test (interp-expr (parse`(get (struct (x 1)) x)))
  1)

(test (interp-expr (parse`(set (struct (x 1)) x 2)))
  1)

(test (interp-expr (parse `(set (struct (x 42)) x 2)))
  42)

(test (interp-expr (parse `(with (b (struct (x 1))) (seqn (set b x 2) (get b x)))))
  2)

(test (interp-expr (parse `(with (b (struct (x 1))) (+ (get b x) (seqn (set b x 2) (get b x))))))
  3)

(test (interp-expr (parse `(with (b (struct (x 1))) (+ (seqn (set b x 2) (get b x)) (get b x)))))
  4)

(test/exn (interp-expr (parse `(get 1 x)))
  "expected record")

(test/exn (interp-expr (parse `(set 1 x (struct (x 2)))))
  "expected record")

(test/exn (interp-expr (parse`(get (struct (x 2)) y)))
  "unknown field")

(test/exn (interp-expr (parse `(set (struct (x 2)) y 3)))
  "unknown field")

(test (interp-expr (parse `(get (struct (x 1) (y 2) (z 3)) x)))
  1)

(test (interp-expr (parse `(get (struct (x 1) (y 2) (z 3)) y)))
  2)

(test (interp-expr (parse `(get (struct (x 1) (y 2) (z 3)) z)))
  3)

(test (interp-expr (parse `(set (struct (x 1) (y 2) (z 3)) x 11)))
  1)

(test (interp-expr (parse `(set (struct (x 1) (y 2) (z 3)) y 11)))
  2)

(test (interp-expr (parse `(set (struct (x 1) (y 2) (z 3)) z 11)))
  3)

(test (interp-expr (parse `(with (r (struct (x 1) (y 2) (z 3))) (seqn (set r x 17) (get r x)))))
  17)

(test (interp-expr (parse `(with (r (struct (x 1) (y 2) (z 3))) (seqn (set r y 17) (get r y)))))
  17)

(test (interp-expr (parse `(with (r (struct (x 1) (y 2) (z 3))) (seqn (set r z 17) (get r z)))))
  17)

(test (interp-expr (parse '((fun (r) (get r x)) (struct (x 1)))))
  1)

(test (interp-expr (parse '((fun (r) (seqn (set r x 5) (get r x))) (struct (x 1)))))
  5)

(test (interp-expr (parse
                    '(((((fun
         (g)
         (fun
          (s)
          (fun
           (r1)
           (fun
            (r2)
            (+
             (get r1 b)
             (seqn
              ((s r1) (g r2))
              (+ (seqn ((s r2) (g r1)) (get r1 b)) (get r2 b))))))))
        (fun (r) (get r a)))
       (fun (r) (fun (v) (set r b v))))
      (struct (a 0) (b 2)))
     (struct (a 3) (b 4)))))
  4)

(test/exn (interp-expr (parse '(get (struct (x 1) (y x)) y)))
  "free identifier")

(test/exn (interp-expr (parse `(get (set (struct (x 42)) x 2) x)))
  "expected record")

;(parse `(get (with (x 1) (struct (x x))) x))
(test (interp-expr (parse `(get (with (x 1) (struct (x x))) x)))
  1)

(test (interp-expr (parse '(with (x (struct (a 1) (b 2) (c 3))) (set x b (seqn (set x b 5) 7)))))
  5)

(test (interp-expr (parse `(with
     (b (struct (x 1) (y (struct (a 1) (b 2))) (z 3)))
     (seqn (set b z 4) (get b z)))))
  4)

(test (interp-expr (parse `(with (b (struct (x (struct (x 111))))) (get (get b x) x))))
  111)

(test (interp-expr (parse `(with
     (b (struct (x 1111)))
     (seqn (seqn (seqn (set b x 0) 0) (seqn (set b x 1) 0)) (get b x)))))
  1)

(test (interp-expr (parse `(with
     (b (struct (x 1111)))
     (seqn (+ (seqn (set b x 0) 0) (seqn (set b x 1) 0)) (get b x)))))
  1)

(test (interp-expr (parse `(with
     (b (struct (x 1111)))
     (seqn (- (seqn (set b x 0) 0) (seqn (set b x 1) 0)) (get b x)))))
  1)

(test (interp-expr (parse `(with
     (b (struct (x 1111)))
     (seqn ((seqn (set b x 0) (fun (x) x)) (seqn (set b x 1) 0)) (get b x)))))
  1)

(test (interp-expr (parse `(with
     (b (struct (x 1111)))
     (seqn
      (set (seqn (set b x 0) (struct (z 111))) z (seqn (set b x 1) 32))
      (get b x)))))
  1)

(test (interp-expr (parse `(with
     (b (struct (x 1111)))
     (seqn
      (set
       (seqn (set b x (+ (get b x) 1)) (struct (z 111)))
       z
       (seqn (set b x (+ (get b x) 1)) 32))
      (get b x)))))
  1113)

(test (interp-expr (parse `(with (b (struct (x 1111))) (get (seqn (set b x 0) b) x))))
  0)

(test (interp-expr (parse `(with
     (b (struct (x 1111)))
     (seqn
      (struct
       (a (seqn (set b x (+ (get b x) (get b x))) 111))
       (b (seqn (set b x (+ (get b x) 1)) 222))
       (c (seqn (set b x (+ (+ (get b x) (get b x)) (get b x))) 222))
       (d (seqn (set b x (+ (get b x) 2)) 222)))
      (get b x)))))
      6671)

(test/exn (interp-expr (parse `(with (s1 (struct)) (with (s2 (struct (a 10))) (get s1 a)))))
  "unknown field")

(test/exn (interp-expr (parse `(with (s1 (struct (b 20))) (with (s2 (struct (a 10))) (get s1 a)))))
  "unknown field")

(test (interp-expr (parse 1))
  1)

(test (interp-expr (parse `(+ 1 2)))
  3)

(test (interp-expr
  (parse `(- (+ 1 2) (+ 1 (- 3 4)))))
  3)

(test (interp-expr
  (parse `(with (x (+ 1 2)) (+ x x))))
  6)

(test (interp-expr (parse `(with (x (+ 1 2)) (with (y (+ x x)) (+ y y)))))
  12)

(test (interp-expr (parse `(with (x (+ 1 2)) (with (x (+ x x)) (+ x x)))))
  12)

(test (interp-expr (parse `(with (x 2) (with (f (fun (y) (- x y))) (f 1)))))
  1)

(test (interp-expr (parse `(((fun (x) (fun (y) (+ x y))) 1) 2)))
  3)

;(parse `(((fun (x) (fun (x) (+ x x))) 1) 2))
(test (interp-expr (parse `(((fun (x) (fun (x) (+ x x))) 1) 2)))
  4)

(test/exn (interp-expr (parse `(+ 1 (fun (x) x))))
  "expected number")

(test/exn (interp-expr (parse `(- (fun (x) x) 1)))
  "expected number")

(test/exn (interp-expr (parse `(1 2)))
  "expected function")

(test/exn (interp-expr (parse `x))
  "free identifier")

(test/exn (interp-expr (parse '(0 Q)))
 "free identifier")

