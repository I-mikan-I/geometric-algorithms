#lang racket
(require scapegoat-tree)
(require (prefix-in bh: pfds/heap/binomial))
(require data/order)
;(require (submod "utils.rkt" no-contract))
(require "utils.rkt")

(provide (all-defined-out))

(module* debug racket
  (require (submod ".."))
  (provide (prefix-out raw: (all-from-out (submod ".."))))
  (provide (contract-out [23tree-empty? (-> any/c boolean?)]
                         [23tree-balanced? (-> any/c boolean?)]
                         [breakpoint? (-> any/c boolean?)]
                         [point? (-> any/c boolean?)]
                         [breakpoint->x (-> breakpoint? number? number?)]
                         [cmp-bp-p (-> breakpoint? point? number? boolean?)]
                         [breakpoint-merge (-> breakpoint? breakpoint? breakpoint?)]
                         [23tree
                          (-> (-> breakpoint? point? boolean?)
                              (-> breakpoint? breakpoint? breakpoint?)
                              (and/c 23tree-empty? 23tree-balanced?))]
                         [23tree-split
                          (-> 23tree-balanced? point? (and/c 23tree-balanced? (not/c 23tree-empty?)))]
                         [23tree-remove (-> 23tree-balanced? point? 23tree-balanced?)]
                         [23tree-inorder (-> 23tree-balanced? list?)]
                         [23tree-get-triple
                          (-> 23tree-balanced?
                              point?
                              (values (or/c point? #f) (or/c point? #f) (or/c point? #f)))])))

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
(struct point (x y [removed #:auto #:mutable])
  #:auto-value #f
  #:transparent)
(struct breakpoint (p1 p2) #:transparent)
(struct circle (x y bp [removed #:auto #:mutable]) #:auto-value #f #:transparent)

(struct root (cmp? combine-keys t))
(struct node2 (l k r))
(struct node3 (l k1 m k2 r))
(struct OF2 (t1 k t2))
(struct OF3 (t1 k1 t2 k2 t3))
(struct UF (t))
(struct TI (t))
(define (23tree cmp? combine-keys)
  (root cmp? combine-keys #f))

(define 23tree-empty?
  (match-lambda
    [(struct* root ([t root_node])) (not root_node)]))

(define/match (height n)
  [((node2 l k r)) (+ 1 (height l))]
  [((node3 l k1 m k2 r)) (+ 1 (height l))]
  [(_) 0])
(define node-balanced
  (match-lambda
    [(node2 l _ r) (and (equal? (height l) (height r)) (node-balanced l) (node-balanced r))]
    [(node3 l _ m _ r)
     (and (equal? (height l) (height r))
          (equal? (height r) (height m))
          (node-balanced l)
          (node-balanced r)
          (node-balanced m))]
    [_ #t]))

(define 23tree-balanced?
  (match-lambda
    [(struct* root ([t root_node])) (node-balanced root_node)]))

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
    [(or (list (cons #f l) k r) (list l k (cons #f r))) (cons #f (balance-d l k r))]
    [(list (cons (cright k_) l) k r) (cons #f (balance-d l (combine-keys-balance k_ k) r))]
    [(list l k (cons (cleft k_) r)) (cons #f (balance-d l (combine-keys-balance k k_) r))]
    [(or (list (cons op l) k r) (list l k (cons op r))) (cons op (balance-d l k r))]
    ; node3
    [(or (list (cons #f l) k1 m k2 r) (list l k1 (cons #f m) k2 r) (list l k1 m k2 (cons #f r)))
     (cons #f (balance-d l k1 m k2 r))]
    [(list (cons (cright k_) l) k1 m k2 r)
     (cons #f (balance-d l (combine-keys-balance k_ k1) m k2 r))]
    [(list l k1 (cons (cleft k_) m) k2 r) (cons #f (balance-d l (combine-keys-balance k1 k_) m k2 r))]
    [(list l k1 (cons (cright k_) m) k2 r)
     (cons #f (balance-d l k1 m (combine-keys-balance k_ k2) r))]
    [(list l k1 m k2 (cons (cleft k_) r)) (cons #f (balance-d l k1 m (combine-keys-balance k2 k_) r))]
    [(or (list (cons op l) k1 m k2 r) (list l k1 m k2 (cons op r)))
     (cons op (balance-d l k1 m k2 r))]))

(define (_23tree-split t v cmp?)
  (match t
    [#f (TI v)]
    [(struct point _) (OF3 t (breakpoint t v) v (breakpoint v t) t)]
    [(struct node2 (l k r))
     (if (cmp? k v) (balance (_23tree-split l v cmp?) k r) (balance l k (_23tree-split r v cmp?)))]
    [(struct node3 (l k1 m k2 r))
     (cond
       [(cmp? k1 v) (balance (_23tree-split l v cmp?) k1 m k2 r)]
       [(cmp? k2 v) (balance l k1 (_23tree-split m v cmp?) k2 r)]
       [else (balance l k1 m k2 (_23tree-split r v cmp?))])]))

(define (23tree-inorder t)
  (match-define (root cmp? _ root-node) t)
  (let rec ([node root-node])
    (match node
      [(node2 l k r) (append (rec l) `(,k) (rec r))]
      [(node3 l k1 m k2 r) (append (rec l) `(,k1) (rec m) `(,k2) (rec r))]
      [v `(,v)])))

(define (_rightmost-val t)
  (match t
    [(node2 l k r) (_rightmost-val r)]
    [(node3 l k1 m k2 r) (_rightmost-val r)]
    [val val]))

(define (_leftmost-val t)
  (match t
    [(node2 l k r) (_leftmost-val l)]
    [(node3 l k1 m k2 r) (_leftmost-val l)]
    [val val]))

(define (_23tree-left-val t p cmp?)
  (match t
    [(node2 lt k rt)
     (cond
       [(cmp? k p) (_23tree-left-val lt p cmp?)]
       [else (or (_23tree-left-val rt p cmp?) (_leftmost-val lt))])]
    [(node3 lt k1 mt k2 rt)
     (cond
       [(cmp? k1 p) (_23tree-left-val lt p cmp?)]
       [(cmp? k2 p) (or (_23tree-left-val mt p cmp?) (_rightmost-val lt))]
       [else (or (_23tree-left-val rt p cmp?) (_rightmost-val mt))])]
    [val #f]))

(define (_23tree-right-val t p cmp?)
  (match t
    [(node2 lt k rt)
     (cond
       [(cmp? k p) (or (_23tree-right-val lt p cmp?) (_leftmost-val rt))]
       [else (_23tree-right-val rt p cmp?)])]
    [(node3 lt k1 mt k2 rt)
     (cond
       [(cmp? k1 p) (or (_23tree-right-val lt p cmp?) (_leftmost-val mt))]
       [(cmp? k2 p) (or (_23tree-right-val mt p cmp?) (_leftmost-val rt))]
       [else (_23tree-right-val rt p cmp?)])]
    [val #f]))

(define (_23tree-ref t p cmp?)
  (match t
    [(node2 l k r)
     (cond
       [(cmp? k p) (_23tree-ref l)]
       [else (_23tree-ref r)])]
    [(node3 l k1 m k2 r)
     (cond
       [(cmp? k1 p) (_23tree-ref l)]
       [(cmp? k2 p) (_23tree-ref m)]
       [else (_23tree-ref r)])]
    [v v]))

(define/match (23tree-ref t p)
  [((struct root (cmp? _ t)) p) (_23tree-ref t p cmp?)])
(define/match (23tree-left-val t p)
  [((struct root (cmp? _ t)) p) (_23tree-left-val t p cmp?)])
(define/match (23tree-right-val t p)
  [((struct root (cmp? _ t)) p) (_23tree-right-val t p cmp?)])

(define (arc->breakpoint t p)
  (let ([left (23tree-left-val t p)]) (if left (breakpoint left p) ('leftmost))))

(define (breakpoint->arc t bp l)
  (define x (breakpoint->x bp l))
  (match-define (root cmp? _ t) t)
  (match t
    [(node2 lt k rt)
     #:when (eq? bp 'leftmost)
     (_leftmost-val lt)]
    [(node2 lt (== bp) rt) (_leftmost-val rt)]
    [(node2 lt k rt)
     #:when (< x (breakpoint->x k l))
     (breakpoint->arc lt bp l)]
    [(node2 lt k rt) (breakpoint->arc rt bp l)]
    [(node3 lt k1 mt k2 rt)
     #:when (eq? bp 'leftmost)
     (_leftmost-val lt)]
    [(node3 lt (== bp) mt k2 rt) (_leftmost-val mt)]
    [(node3 lt k1 mt (== bp) rt) (_leftmost-val rt)]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k1))
     (breakpoint->arc lt bp l)]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k2))
     (breakpoint->arc mt bp l)]
    [(node3 lt k1 mt k2 rt) (breakpoint->arc rt bp l)]))

(define (_rightmost-key t)
  (match t
    [(node2 l k r) (or (_rightmost-key r) k)]
    [(node3 l k1 m k2 r) (or (_rightmost-key r) k2)]
    [_ #f]))

(define (_leftmost-key t)
  (match t
    [(node2 l k r) (or (_leftmost-key l) k)]
    [(node3 l k1 m k2 r) (or (_leftmost-key l) k1)]
    [_ #f]))

(define (_23tree-left-bp t bp l)
  (define x (breakpoint->x bp l))
  (match t
    [(node2 lt (== bp) rt) (_rightmost-key lt)]
    [(node2 lt k rt)
     #:when (< x (breakpoint->x k l))
     (_23tree-left-bp lt bp l)]
    [(node2 lt k rt) (or (_23tree-left-bp rt bp l) k)]
    [(node3 lt (== bp) mt k2 rt) (_rightmost-key lt)]
    [(node3 lt k1 mt (== bp) rt) (or (_rightmost-key mt) k1)]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k1 l))
     (_23tree-left-bp lt bp l)]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k2 l))
     (or (_23tree-left-bp mt bp l) k1)]
    [(node3 lt k1 mt k2 rt) (or (_23tree-left-bp rt bp l) k2)]
    [_ #f]))

(define (23tree-left-bp t bp l)
  (match t
    [(root _ _ t) (_23tree-left-bp t bp l)]))

(define (_23tree-right-bp t bp l)
  (define x (breakpoint->x bp l))
  (match t
    [(node2 lt (== bp) rt) (_leftmost-key lt)]
    [(node2 lt k rt)
     #:when (< x (breakpoint->x k l))
     (or (_23tree-right-bp lt bp l) k)]
    [(node2 lt k rt) (_23tree-right-bp rt bp l)]
    [(node3 lt (== bp) mt k2 rt) (or (_leftmost-key mt) k2)]
    [(node3 lt k1 mt (== bp) rt) (_leftmost-key rt)]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k1 l))
     (or (_23tree-right-bp lt bp l) k1)]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k2 l))
     (or (_23tree-right-bp mt bp l) k2)]
    [(node3 lt k1 mt k2 rt) (_23tree-right-bp rt bp l)]
    [_ #f]))

(define (23tree-right-bp t bp l)
  (match t
    [(root _ _ t) (_23tree-right-bp t bp l)]))

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
  (match-let ([(struct root (cmp? _ root-node)) t])
    (match (_23tree-split root-node v cmp?)
      [(TI root-node) (struct-copy root t [t root-node])]
      [(OF2 l k r) (struct-copy root t [t (node2 l k r)])]
      [(OF3 l k1 m k2 r) (struct-copy root t [t (node3 l k1 m k2 r)])])))

(define (23tree-remove t v)
  (match-let ([(root cmp? combine-keys t) t])
    (_23tree-remove t v cmp? combine-keys)))

;; TODO ------------------------------------------

(struct vertex (neighbors) #:transparent)

(define (breakpoint->x bp l)
  (match-let ([(breakpoint (point x1 y1 _) (point x2 y2 _)) bp])
    (printf "x1: ~v y1: ~v x2: ~v y2: ~v l: ~v\n" x1 y1 x2 y2 l)
    ; arc point1: (l - y) = sqrt ((x1 - x)^2 + (y1 - y)^2)
    ; .. (l - y)^2 = (x1 - x)^2 + (y1 - y)^2
    ; .. l^2 -2ly + y^2 = x1^2 - 2x1x + x^2 + y1^2 - 2y1y + y^2
    ; .. -2ly + 2y1y = -l^2 + x1^2 -2x1x + x^2 + y1^2
    ; y = (1/2(y1 - l)) * (x^2 -2x1*x + y1^2 + x1^2 -l^2)
    ; arc point2: y = (1/2(y2 - l)) * (x^2 -2x2*x + y2^2 + x2^2 -l^2)
    ; (1/2(y1 - l) := f1) * (x^2 -2x1*x + y1^2 + x1^2) = (1/2(y2 - l) := f2) * (x^2 -2x2*x + y2^2 + x2^2)
    ; f1*x^2 - 2f1x1*x - f2*x^2 + 2f2x2*x = (f2y2^2 + f2x2^2 - f1y1^2 - f1x1^2 + f1l^2 - f2l^2 := r)
    ; (f2 - f1)x^2 + 2(f1x1 - f2x2)x + r = 0
    ; d/dx 2(f2 - f1)x + 2(f1x1 - f2x2) = y
    ; difference: arc2 - arc
    ;   ==> f2x^2 - 2f2x2x + f2y2^2 + f2x2^2 - f1x^2 + 2f1x1x - f1y1^2 - f1x1^2
    ;   ==> (f2 - f1)x^2 + 2(f1x1 - f2x2)x + r
    ; ==> need decreasing side of function, f1 > f2 means on the right, f2 >= f1 means on the left
    ; ==> either -2(f2x2 - f1x2) - sqrt (4(f2x2 - f1x1)^2 - 4((f1 - f2)r)) / 2(f1 - f2) or ... + ...
    (let* ([f1 (/ 1 (* 2 (- y1 l)))]
           [f2 (/ 1 (* 2 (- y2 l)))]
           [r (+ (* f2 (* y2 y2))
                 (* f2 (* x2 x2))
                 (- (* f1 (* y1 y1)))
                 (- (* f1 (* x1 x1)))
                 (* l l (- f1 f2)))]
           [a (- f2 f1)]
           [b (* 2 (- (* f1 x1) (* f2 x2)))]
           [c r]
           [op -])
      (/ (op (- b) (sqrt (- (* b b) (* 4 a c)))) (* 2 a)))))
;; p is list of points
(define (cmp-bp-p bp p l)
  (let ([bp-x (breakpoint->x bp l)])
    (printf "got bp-x: ~v\n" bp-x)
    (< (point-x p) bp-x)))

(define/match (breakpoint-merge l r)
  [((breakpoint l1 _) (breakpoint _ r2)) (breakpoint l1 r2)])

(define (circle-center p1 p2 p3)
  (match-let ([(point x1 y1 _) p1]
              [(point x2 y2 _) p2]
              [(point x3 y3 _) p3])
    (let* ([s1 (+ (* x1 x1) (* y1 y1))]
           [s2 (+ (* x2 x2) (* y2 y2))]
           [s3 (+ (* x3 x3) (* y3 y3))]
           [b (+ (* s1 (- y2 y3)) (* s2 (- y3 y1)) (* s3 (- y1 y2)))]
           [a (+ (* x1 (- y2 y3)) (- (* y1 (- x2 x3))) (* x2 y3) (- (* x3 y2)))]
           [c (+ (* s1 (- x3 x2)) (* s2 (- x1 x3)) (* s3 (- x2 x1)))])
      (point (- (/ b (* 2 a))) (- (/ c (* 2 a)))))))

; points define arcs at the leafs of our 2-3 tree.
; we need to map circle event -> arc
;   can be done via breakpoint: breakpoints are unique
; we need to map arc -> circle event
;   can also be done via pointer
; arc uniquely defined by left breakpoint
; have to query: breakpoint -> arc, arc -> left arc/right arc

(define (voronoi . p)
  (define l (box 0))
  (define (bp-cmp breakpoint site)
    (void))
  (define (combine-keys l r)
    (void))
  (define queue (apply bh:heap (lambda (p1 p2) ((point-y p1) . > . (point-y p2))) p))
  (define tree (23tree bp-cmp combine-keys))

  (define (event p tree queue arc_ce_map)
    (match p
      [(point x y removed) ; site event
       (if (23tree-empty? tree)
           (23tree-split p)
           (let* ([m (23tree-ref tree p)]
                  [m-ce (dict-ref arc_ce_map (arc->breakpoint m) #f)]
                  [l (23tree-left-val tree m)]
                  [r (23tree-right-val tree m)])
             (begin
               (if (point-circle-event m) (set-circle-removed! (point-circle-event m) #t) (void))
               (let ([tree (23tree-split tree p)])
                 (let-values ([(ml _ mr) (23tree-get-triple tree p)])
                   (let* ([left-ce (if (point? ml)
                                       (match-let ([(point cx cy _ _) (circle-center l ml p)])
                                         (if (<= cy y) (point cx cy #f #t) #f))
                                       #f)]
                          [right-ce (if (point? mr)
                                        (match-let ([(point cx cy _ _) (circle-center p mr r)])
                                          (if (<= cy y) (point cx cy #f #t) #f))
                                        #f)]
                          [removed_ce (dict-ref arc_ce_map m #f)]
                          [arc_ce_map (dict-remove arc_ce_map m)]
                          [arc_ce_map (if left-ce (dict-set arc_ce_map ml left-ce) arc_ce_map)]
                          [arc_ce_map (if right-ce (dict-set arc_ce_map mr right-ce) arc_ce_map)]
                          [queue (if left-ce (bh:insert left-ce queue) queue)]
                          [queue (if right-ce (bh:insert right-ce queue) queue)])
                     (begin
                       (if removed_ce (set-point-removed! removed_ce #t) (void))
                       (values tree queue arc_ce_map))))))))]
      [(circle x y bp removed) ; circle event
       (let ([l (23tree-left-bp tree bp y)]
             [r (23tree-right-bp tree bp y)])
         (void))]))

  (let while ([queue queue]
              [tree tree]
              [diagram (hash)])
    (if (bh:empty? queue)
        (void)
        (let ([next (bh:find-min/max queue)]
              [queue (bh:delete-min/max queue)])
          (if (point? next) ((event p) tree queue l) (while queue tree))))))

(module* test-tree racket
  (require (submod ".." debug))
  (require plot)

  (plot-new-window? #t)
  (define t (23tree (lambda (bp p) (cmp-bp-p bp p (raw:point-y p))) breakpoint-merge))
  (define points (list (raw:point 5 14) (raw:point 15 12) (raw:point 25 10) (raw:point 13 9)))
  (set! t
        (for/fold ([t t]) ([p points])
          (printf "inorder: ~v\n" (23tree-inorder t))
          (23tree-split t p)))

  (define/match (arc p l)
    ; y = (1/2(y1 - l)) * (x^2 -2x1*x + y1^2 + x1^2 -l^2)
    [((raw:point x1 y1 _ _) l)
     (lambda (x)
       (* (/ 1 (* 2 (- y1 l))) (+ (* x x) (- (* 2 x1 x)) (* x1 x1) (* y1 y1) (- (* l l)))))])
  (plot (map (lambda (p) (function (arc p 8.99) 0 200 #:y-min 0 #:y-max 400)) points))
  (printf "inorder: ~v\n" (23tree-inorder t))
  (printf "get-triple ~v ~v\n"
          (raw:point 11 9)
          (call-with-values (lambda () (23tree-get-triple t (raw:point 11 8.99))) list)))

(module+ test
  (define data '((0 . 1) (5 . 1) (8 . 1) (100 . 1) (101 . 1) (-20 . 1)))
  (apply scanline data)
  (set! data '((0 . 1) (5 . 3) (8 . 5) (100 . 100) (101 . 23) (-20 . -2) (-19 . -10)))
  (apply scanline data))
