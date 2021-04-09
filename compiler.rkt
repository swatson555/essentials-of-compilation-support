#lang racket
(require racket/set
         racket/stream
         racket/dict
         racket/fixnum)
(require "interp-R0.rkt")
(require "interp-R1.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; uniquify : R1 -> R1
(define (uniquify-exp alist)
  (lambda (e)
    (match e
      [(? symbol?) (dict-ref alist e)]
      [(? integer?) e]
      [`(let ([,x ,e]) ,body)
       (define n (gensym))
       (define u (uniquify-exp (dict-set alist x n)))
       `(let ([,n ,(u e)]) ,(u body))]
      [`(,op ,es ...)
       `(,op ,@(for/list ([e es]) ((uniquify-exp alist) e)))])))

(define (uniquify e)
  (match e
    [`(program ,info ,exp)
     `(program ,info ,((uniquify-exp '()) exp))]))


;; remove-complex-opera* : R1 -> R1
(define (rco-exp e*)
  (define (make-let-exp x* e* body)
    (if (null? x*)
        body
        `(let ([,(car x*) ,(car e*)])
           ,(make-let-exp (cdr x*) (cdr e*) body))))
  (match e*
    [(? symbol?)  e*]
    [(? integer?) e*]
    [`(let ([,x ,e]) ,body)
     `(let ([,x ,(rco-exp e)]) ,(rco-exp body))]
    [else
     (let rco-arg ([e* e*] [t* '()] [te* '()] [re* '()])
       (if (null? e*)
           (make-let-exp t* te* (reverse re*))
           (let ([e (car e*)])
             (match e
               [(? symbol?)  (rco-arg (cdr e*) t* te* (cons e re*))]
               [(? integer?) (rco-arg (cdr e*) t* te* (cons e re*))]
               [else (define t (gensym))
                     (rco-arg (cdr e*) (cons t t*) (cons (rco-exp e) te*) (cons t re*))]))))]))

(define (remove-complex-opera* e)
  (match e
    [`(program ,info ,exp)
     `(program ,info ,(rco-exp exp))]))


;; explicate-control : R1 -> C0
(define (explicate-control-assign x e t)
  (match e
    [`(let ([,x0 ,e0]) ,b)
     (explicate-control-assign x0 e0 (explicate-control-assign x b t))]
    [else `(seq (assign ,x ,e) ,t)]))

(define (explicate-control-tail e)
  (match e
    [`(let ([,x ,e]) ,b)
     (explicate-control-assign x e (explicate-control-tail b))]
    [else `(return ,e)]))

(define (explicate-control e)
  (match e
    [`(program ,info ,exp)
     `(program ,info ,(dict-set '() 'start (explicate-control-tail exp)))]))


;; uncover-locals : C0 -> C0
(define (uncover seqs)
  (if (null? seqs)
      '()
      (let loop ([seq (cdar seqs)])
        (match seq
          [`(seq (assign ,x ,v) ,tail) (cons x (loop tail))]
          [`(return ,exp) (uncover (cdr seqs))]))))

(define (uncover-locals e)
  (match e
    [`(program ,info ,labels)
     `(program ,(dict-set info 'locals (uncover labels)) ,labels)]))


;; select-instructions : C0 -> pseudo-x86
(define (select-instructions-arg arg)
  (match arg
    [(? symbol?)  `(var ,arg)]
    [(? integer?) `(int ,arg)]))

(define (select-instructions-stmt stmt)
  (match stmt
    [`(assign ,var (+ ,arg0 ,arg1)) `((movq ,(select-instructions-arg arg0) (var ,var))
                                      (addq ,(select-instructions-arg arg1) (var ,var)))]
    [`(assign ,var (- ,arg0))       `((movq ,(select-instructions-arg arg0) (var ,var))
                                      (negq (var ,var)))]
    [`(assign ,var (read))          `((callq read_int)
                                      (movq (reg rax) (var ,var)))]
    [`(assign ,var ,arg0)           `((movq ,(select-instructions-arg arg0) (var ,var)))]))

(define (select-instructions-tail tail)
  (match tail
    [`(return (+ ,arg0 ,arg1)) `((movq ,(select-instructions-arg arg0) (reg rax))
                                 (addq ,(select-instructions-arg arg1) (reg rax))
                                 (jmp conclusion))]
    [`(return (- ,arg0))       `((movq ,(select-instructions-arg arg0) (reg rax))
                                 (negq (reg rax))
                                 (jmp conclusion))]
    [`(return (read))          `((callq read_int)
                                 (jmp conclusion))]
    [`(return ,arg0)           `((movq ,(select-instructions-arg arg0) (reg rax))
                                 (jmp conclusion))]
    [`(seq ,stmt ,tail)
     (append (select-instructions-stmt stmt)
             (select-instructions-tail tail))]))

(define (select-instructions e)
  (match e
    [`(program ,info ,labels)
     `(program ,info ,(dict-set labels
                                'start
                                (append '(block ()) (select-instructions-tail (dict-ref labels 'start)))))]))


;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes-instr homes instrs)
  (map (lambda (instr)
         (match instr
           [`(,op (var ,op0) (var ,op1))
            `(,op ,(dict-ref homes op0) ,(dict-ref homes op1))]
           [`(,op (var ,op0) ,op1)
            `(,op ,(dict-ref homes op0) ,op1)]
           [`(,op ,op0 (var ,op1))
            `(,op ,op0 ,(dict-ref homes op1))]
           [`(,op (var ,op0))
            `(,op ,(dict-ref homes op0))]
           [else instr]))
       instrs))

(define (assign-homes-label info labels)
  (define (homes vars loc)
    (if (null? vars)
        '()
        (cons (cons (car vars) `(deref rbp ,loc))
              (homes (cdr vars) (- loc 8)))))
  (let ([homes-dict (homes (dict-ref info 'locals) -8)])
    (match (dict-ref labels 'start)
      [`(block ,b-info ,instr* ...)
       (dict-set labels 'start (append `(block ,b-info) (assign-homes-instr homes-dict instr*)))])))

(define (assign-homes e)
  (match e
    [`(program ,info ,labels)
     `(program ,info ,(assign-homes-label info labels))]))


;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions-instr instrs)
  (if (null? instrs)
      '()
      (append (match (car instrs)
                [`(,op (deref rbp ,loc0) (deref rbp ,loc1))
                 `((movq (deref rbp ,loc0) (reg rax))
                   (,op (reg rax) (deref rbp ,loc1)))]
                [else (list (car instrs))])
              (patch-instructions-instr (cdr instrs)))))

(define (patch-instructions-label labels)
  (match (dict-ref labels 'start)
    [`(block ,b-info ,instr* ...)
     (dict-set labels 'start (append `(block ,b-info) (patch-instructions-instr instr*)))]))

(define (patch-instructions e)
  (match e
    [`(program ,info ,labels)
     `(program ,info ,(patch-instructions-label labels))]))


;; print-x86 : x86 -> string
(define (emit-instrs instrs)
  (if (null? instrs)
      "\n"
      (string-append "\t"
                     (match (car instrs)
                       [`(jmp ,label) (format "jmp ~a" label)]
                       [`(callq ,label) (format "callq ~a" label)]
                       [`(,op (reg ,r)) (format "~a %~a" op r)]
                       [`(,op (int ,i)) (format "~a $~a" op i)]
                       [`(,op (deref rbp ,loc)) (format "~a ~a(%rbp)" op loc)]
                       [`(,op (reg ,r) (int ,i)) (format "~a %~a, $~a" op r i)]
                       [`(,op (int ,i) (reg ,r)) (format "~a $~a, %~a" op i r)]
                       [`(,op (reg ,r) (deref rbp ,loc)) (format "~a %~a, ~a(%rbp)" op r loc)]
                       [`(,op (int ,i) (deref rbp ,loc)) (format "~a $~a, ~a(%rbp)" op i loc)]
                       [`(,op (deref rbp ,loc) (reg ,r)) (format "~a ~a(%rbp), %~a" op loc r)]
                       [`(,op (deref rbp ,loc) (int ,i)) (format "~a ~a(%rbp), $~a" op loc i)])
                     "\n" (emit-instrs (cdr instrs)))))

(define (emit-labels labels)
  (match (dict-ref labels 'start)
    [`(block ,b-info ,instr* ...)
     (string-append "start:\n"
                    (emit-instrs instr*))]))

(define (emit-prelude size)
  (format "	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $~a, %rsp
	jmp start
conclusion:
	addq $~a, %rsp
	popq %rbp
	retq
" size size))

(define (print-x86 e)
  (match e
    [`(program ,info ,labels)
     (define stack-size
       ;; Align to 16-bytes
       (let ([size (* 8 (length (dict-ref info 'locals)))])
         (if (zero? (modulo size 16))
             size
             (+ 8 size))))
     (string-append (emit-labels labels)
                    (emit-prelude stack-size))]))

(define (compile exp)
  (define gcc (process "gcc runtime.c -x assembler -"))
  (define assembler-stdin (list-ref gcc 0))
  (define assembler-stdout (list-ref gcc 1))
  (define assembler-id (list-ref gcc 2))
  (define assembler-stderr (list-ref gcc 3))
  (define assembler-comm (list-ref gcc 4))
  (fprintf assembler-stdout
           (print-x86
            (patch-instructions
             (assign-homes
              (select-instructions
               (uncover-locals
                (explicate-control
                 (remove-complex-opera*
                  (uniquify `(program () ,exp))))))))))
  (close-output-port assembler-stdout)
  (printf (port->string assembler-stdin #:close? #t))
  (printf (port->string assembler-stderr #:close? #t))
  (assembler-comm 'wait)
  (system "./a.out || echo $?"))
