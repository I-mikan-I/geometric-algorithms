#lang racket
(require scapegoat-tree)
(require (prefix-in bh: pfds/heap/binomial))
(require data/order)
;(require (submod "utils.rkt" no-contract))
(require "utils.rkt")

(define ((dist p1) p2)
  (match-define-values ((cons x1 y1) (cons x2 y2)) (values p1 p2))
  (sqrt ((sqr (abs (x1 . - . x2))) . + . (sqr (abs (y1 . - . y2))))))

; points = list of (x . y)
(define (scanline . points)
  (let* ([sorted (sort points < #:key car)]
         [tree (make-scapegoat-tree real-order)])
    (if (empty? sorted)
        #f
        (let scan ([tree (dict-set tree (cdr (first sorted)) (car (first sorted)))]
                   [to_process (rest sorted)]
                   [in_tree_ (queue (first sorted))]
                   [min_dist #xFFFFFFFFF])
          (printf "Current min: ~v\n" min_dist)
          (match to_process
            [(list (cons x y) tail ...)
             (define-values (to_remove in_tree)
               ((deq-while (lambda (p2) (> (abs (- x (car p2))) min_dist))) in_tree_))
             (define pruned_tree
               (for/fold ([tree tree]) ([x to_remove])
                 (dict-remove tree (cdr x))))
             (define within-rect
               (dict-sublist pruned_tree
                             (- y min_dist)
                             (+ y min_dist)
                             #:mapper (lambda (x y) (cons y x))))
             (println `("pruned: " ,(dict->list pruned_tree)))
             (println `("unpruned " ,(dict->list tree)))
             (printf "Within rect: ~v\n" within-rect)
             (printf "To remove: ~v\n" to_remove)
             (define dists (cons min_dist (map (dist (cons x y)) within-rect)))
             (scan (dict-set pruned_tree y x) tail (enq in_tree (cons x y)) (apply min dists))]
            [_ min_dist])))))

;; voronoi diagrams
(struct p (x y [removed #:auto #:mutable]) #:auto-value #t)
(struct bp (p1 p2))

(struct root (cmp? combine-keys t))
(struct node2 (l k r))
(struct node3 (l k1 m k2 r))
(struct OF2 (t1 k t2))
(struct OF3 (t1 k1 t2 k2 t3))
(struct UF (t))
(struct TI (t))
(define (23tree cmp?)
  (root cmp? #f))

(define balance
  (match-lambda*
    [(or (list (struct TI (l)) k r) (list l k (struct TI (r)))) (TI (node2 l k r))]
    [(or (list (struct OF2 (l k1 m)) k2 r) (list l k1 (struct OF2 (m k2 r))))
     (TI (node3 l k1 m k2 r))]
    [(or (list (struct OF3 (l k1 m1 k2 m2)) k3 r) (list l k1 (struct OF3 (m1 k2 m2 k3 r))))
     (OF2 (node2 l k1 m1) k2 (node2 m2 k3 r))]
    ; node3
    [(or (list (struct TI (l)) k1 m k2 r)
         (list l k1 (struct TI (m)) k2 r)
         (list l k1 m k2 (struct TI (r))))
     (node3 l k1 m k2 r)]
    [(or (list (struct OF2 (l1 k1 m1)) k2 m2 k3 r)
         (list l1 k1 (struct OF2 (m1 k2 m2)) k3 r)
         (list l1 k1 m1 k2 (struct OF2 (m2 k3 r))))
     (OF2 (node2 l1 k1 m1) k2 (node2 m2 k3 r))]
    [(or (list (struct OF3 (l1 k1 m1 k2 m2)) k3 m3 k4 r)
         (list l1 k1 (struct OF3 (m1 k2 m2 k3 m3)) k4 r)
         (list l1 k1 m1 k2 (struct OF3 (m2 k3 m3 k4 r))))
     (OF2 (node3 l1 k1 m1 k2 m2) k3 (node2 m3 k4 r))]))

(define balance-d
  (match-lambda*
    [(or (list (TI l) k r) (list l k (TI r))) (TI (node2 l k r))]
    [(or (list (UF l) k1 (node2 m k2 r)) (list (node2 l k1 m) k2 (UF r))) (UF (node3 l k1 m k2 r))]
    [(or (list (UF l) k1 (node3 m1 k2 m2 k3 r)) (list (node3 l k1 m1 k2 m2) k3 (UF r)))
     (TI (node2 (node2 l m1 k2) (node2 m2 k3 r)))]
    ; node3
    [(or (list (TI l) k1 m k2 r) (list l k1 (TI m) k2 r) (list l k1 m k2 (TI r)))
     (TI (node3 l k1 m k2 r))]
    [(list (UF l) k1 (node2 m1 k2 m2) k3 r) (TI (node2 (node3 l k1 m1 k2 m2) k3 r))]
    [(list (UF l) k1 (node3 m1 k2 m2 k3 m3) k4 r)
     (TI (node3 (node2 l k1 m1) k2 (node2 m2 k3 m3) k4 r))]

    [(or (list l k1 (UF m1) k2 (node2 m2 k3 r)) (list l k1 (node2 m1 k2 m2) k3 (UF r)))
     (TI (node2 l k1 (node3 m1 k2 m2 k3 r)))]
    [(or (list l k1 (UF m1) k2 (node3 m2 k3 m3 k4 r)) (list l k1 (node3 m1 k2 m2 k3 m3) k4 (UF r)))
     (TI (node3 l k1 (node2 m1 k2 m2) k3 (node2 m3 k4 r)))]))

(struct cleft (k))
(struct cright (k))
(define (combine combine-keys-balance)
  (match-lambda*
    [(or (list (cons #f l) k r) (list l k (cons #f r))) (cons #f (balance l k r))]
    [(list (cons (cright k_) l) k r) (cons #f (balance l (combine-keys-balance k_ k) r))]
    [(list l k (cons (cleft k_) r)) (cons #f (balance l (combine-keys-balance k k_) r))]
    [(or (list (cons op l) k r) (list l k (cons op r))) (cons op (balance l k r))]
    ; node3
    [(or (list (cons #f l) k1 m k2 r) (list l k1 (cons #f m) k2 r) (list l k1 m k2 (cons #f r)))
     (cons #f (balance l k1 m k2 r))]
    [(list (cons (cright k_) l) k1 m k2 r) (cons #f (balance l (combine-keys-balance k_ k1) m k2 r))]
    [(list l k1 (cons (cleft k_) m) k2 r) (cons #f (balance l (combine-keys-balance k1 k_) m k2 r))]
    [(list l k1 (cons (cright k_) m) k2 r) (cons #f (balance l k1 m (combine-keys-balance k_ k2) r))]
    [(list l k1 m k2 (cons (cleft k_) r)) (cons #f (balance l k1 m (combine-keys-balance k2 k_) r))]
    [(or (list (cons op l) k1 m k2 r) (list l k1 m k2 (cons op r))) (cons op (balance l k1 m k2 r))]))

(define (_23tree-split t v cmp?)
  (match t
    [#f v]
    [(struct p _) (OF3 p (bp p v) v (bp v p) p)]
    [(struct node2 (l k r))
     (if (cmp? k v) (balance (_23tree-split l v) k r) (balance l k (_23tree-split r v)))]
    [(struct node3 (l k1 m k2 r))
     (cond
       [(cmp? k1 v) (balance (_23tree-split l v) k1 m k2 r)]
       [(cmp? k2 v) (balance l k1 (_23tree-split m v) k2 r)]
       [else (balance l k1 m k2 (_23tree-split r v))])]))

(define (_23tree-remove t v cmp? combine-keys)
  (define combine-inst (combine combine-keys))
  (match t
    [(node3 l k1 (== v) k2 r) (cons #f (TI (node2 l (combine-keys k1 k2) r)))]
    [(node3 (== v) k1 m k2 r) (cons (cleft k1) (TI (node2 m k2 r)))]
    [(node3 l k1 m k2 (== v)) (cons (cright k2) (TI (node2 l k1 m)))]
    [(node3 l k1 m k2 r)
     (cond
       [(cmp? k1 v) (combine-inst (_23tree-remove l v cmp? combine) k1 m k2 r)]
       [(cmp? k2 v) (combine-inst l k1 (_23tree-remove m v cmp? combine) k2 r)]
       [else (combine-inst l k1 m k2 (_23tree-remove r v cmp? combine))])]
    [(node2 (== v) k r) (cons (cleft k) (UF r))]
    [(node2 l k (== v)) (cons (cright k) (UF l))]
    [(node2 l k r)
     (cond
       [(cmp? k v) (combine-inst (_23tree-remove l v cmp? combine) k r)]
       [else (combine-inst l k (_23tree-remove r v cmp? combine))])]))

(define (23tree-split t v)
  (match-let ([(struct root (cmp? _ t)) t])
    (_23tree-split t v cmp?)))

(define (23tree-remove t v)
  (match-let ([(root cmp? combine-keys t) t])
    (_23tree-remove t v cmp? combine-keys)))

;; TODO ------------------------------------------

; (define (site-event site)
;   (lambda (tree queue l)
;     (if (rb:empty? tree) ())
;     (void)))

; p is list of points
; (define (voronoi . p)
;   (define l
;     #&
;     0)
;   (define (bp-cmp bp1 bp2)
;     (void))
;   (define queue (apply bh:heap (lambda (p1 p2) ((p-y p1) . > . (p-y p2))) p))
;   (define tree (rb:redblacktree bp-cmp))
;   (let while ([queue queue]
;               [tree tree])
;     (if (bh:empty? queue)
;         (void)
;         (let ([next (bh:find-min/max queue)]
;               [queue (bh:delete-min/max queue)])
;           (if (p? next) ((site-event p) tree queue l) (while queue tree))))))

(module+ test
  (define data '((0 . 1) (5 . 1) (8 . 1) (100 . 1) (101 . 1) (-20 . 1)))
  (apply scanline data)
  (set! data '((0 . 1) (5 . 3) (8 . 5) (100 . 100) (101 . 23) (-20 . -2) (-19 . -10)))
  (apply scanline data))
