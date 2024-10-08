#lang racket
(require racket/dict)
(require data/order)

(define-syntax-rule (unprotected-provides)
  (provide file->string
           deconstruct
           map-deconstruct
           for/fold/list
           list-idx-set
           vector-idx
           list-idx
           push-back))

(unprotected-provides)
(provide (contract-out
          #:unprotected-submodule no-contract
          (rename queue_t?
                  queue?
                  (-> any/c boolean?))
          [queue (->* () #:rest (listof any/c) queue_t?)]
          [enq (-> queue_t? any/c queue_t?)]
          [deq (-> (and/c queue_t? (not/c queue-empty?)) (values any/c queue_t?))]
          [deq-while (-> (-> any/c boolean?) (-> queue_t? (values list? queue_t?)))]
          #:forall a
          [dict-sublist
           (->i ([d ordered-dict?] [start (d) (dict-key-contract d)] [stop (d) (dict-key-contract d)])
                (#:mapper [mapper (d) (-> (dict-key-contract d) (dict-value-contract d) a)])
                [result (listof a)])]
          [queue-empty? (-> queue_t? boolean?)]))

(module+ no-contract
  (unprotected-provides))

(define (file->string path)
  (port->string (open-input-file path)))

(define-syntax deconstruct
  (syntax-rules ()
    [(deconstruct body str) (list->string (body (string->list str)))]
    [(deconstruct body str box-fn) (box-fn (body (string->list str)))]))

(define-syntax map-deconstruct
  (syntax-rules ()
    [(map-deconstruct body lst) (map (lambda (str) (deconstruct body str)) lst)]
    [(map-deconstruct body lst box-fn) (map (lambda (str) (deconstruct body str box-fn)) lst)]))

(define-syntax-rule (for/fold/list ((folder foldee) ...) (iter ...) body)
  (for/fold ([folder foldee] ...
             [results '()]
             #:result results)
            (iter ...)
    (let-values ([(folder ... result) body])
      (values folder ... (append results (list result))))))

(define-syntax list-idx
  (syntax-rules ()
    [(list-idx lst index) (list-ref lst index)]
    [(list-idx lst index ... last) (list-ref (list-idx lst index ...) last)]))

(define-syntax list-idx-set
  (syntax-rules ()
    [(list-idx-set lst pos value) (list-set lst pos value)]
    [(list-idx-set lst first pos ... value)
     (list-set lst first (list-idx-set (list-ref lst first) pos ... value))]))

(define-syntax vector-idx
  (syntax-rules ()
    [(vector-idx vec index) (vector-ref vec index)]
    [(vector-idx vec index ... last) (vector-ref (vector-idx vec index ...) last)]))

; queue

(struct queue_t ([front] [back]) #:transparent)

(define (queue . elems)
  (queue_t elems '()))

(define (enq q e)
  (define back (queue_t-back q))
  (struct-copy queue_t q [back (cons e back)]))

(define (deq q)
  (match q
    [(struct* queue_t ([front (cons h t)] [back _])) (values h (struct-copy queue_t q [front t]))]
    [(struct* queue_t ([front '()] [back '()])) (error "deq: queue empty")]
    [(struct* queue_t ([front '()] [back bk]))
     (let ([fr (reverse bk)]) (values (first fr) (queue_t (rest fr) '())))]))

(define (push-back q e)
  (struct-copy queue_t q [front (cons e (queue_t-front q))]))

(define (queue-empty? q)
  (and (empty? (queue_t-front q)) (empty? (queue_t-back q))))

(define (deq-while c)
  (match-lambda
    [(struct* queue_t ([front (cons h t)] [back bk]))
     #:when (c h)
     (let-values ([(acc q) ((deq-while c) (queue_t t bk))])
       (values (cons h acc) q))]
    [(struct* queue_t ([front '()] [back bk]))
     #:when (not (empty? bk))
     ((deq-while c) (queue_t (reverse bk) '()))]
    [q (values '() q)]))

; dict sublist

(define (dict-sublist dict startincl endincl #:mapper [mapper cons])
  (define start (dict-iterate-least/>=? dict startincl))
  (define end (dict-iterate-least/>? dict endincl))
  (printf "start: ~v end: ~v startidx: ~v endidx: ~v\n" start end startincl endincl)
  (letrec ([gen (lambda (pos)
                  (if (and pos (not (equal? pos end)))
                      (stream-cons #:eager pos (gen (dict-iterate-next dict pos)))
                      empty-stream))])
    (if start
        (for/list ([pos (gen start)])
          (mapper (dict-iterate-key dict pos) (dict-iterate-value dict pos)))
        '())))
