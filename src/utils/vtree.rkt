;; specialized tree structure for voronoi diagrams
#lang typed/racket

(provide 23tree-empty?
         23tree?
         (struct-out point)
         (struct-out breakpoint)
         breakpoint->x
         breakpoint->xy
         cmp-bp-p
         breakpoint-merge
         23tree
         23tree-split
         23tree-remove
         23tree-inorder
         23tree-left-val
         23tree-right-val
         23tree-right-bp
         23tree-left-bp
         23tree-ref
         arc->breakpoint
         breakpoint->arc
         arc->y)

(define-syntax (finalize stx)
  (syntax-case stx (PUSH POP)
    [(finalize (done ...) (PUSH rst ...)) #'(finalize ((done ...) ()) (rst ...))]
    [(finalize ((contexts ... (context ...)) last) (POP rst ...))
     #'(finalize (contexts ... (context ... last)) (rst ...))]
    [(finalize (done ... (last ...)) (atom rst ...))
     #'(finalize (done ... (last ... atom)) (rst ...))]
    [(finalize ((done ...)) ()) #'(done ...)]))

(define-syntax (pattern stx)
  (syntax-case stx (or AP POP PUSH)
    [(pattern (fexps ...)
       (acm ...)
       ((or cs) rst ...)
       (queue ...))
     (with-syntax ([(cs ...) (local-expand #'(pattern ()
                                               (acm ...)
                                               (cs)
                                               (rst ... queue ...))
                                           (syntax-local-context)
                                           #f)])
       #'(pattern (fexps ... cs ...)
           ()
           ()
           ()))]
    [(pattern (fexps ...)
       (acm ...)
       ((or cs cases ...) rst ...)
       (queue ...))
     (with-syntax ([(cs ...) (local-expand #'(pattern ()
                                               (acm ...)
                                               (cs)
                                               (rst ... queue ...))
                                           (syntax-local-context)
                                           #f)])
       #'(pattern (fexps ... cs ...)
           (acm ...)
           ((or cases ...) rst ...)
           (queue ...)))]
    [(pattern fexps
       (acm ...)
       ((fst ...) rst ...)
       (queue ...))
     #'(pattern fexps
         (acm ... PUSH)
         (fst ...)
         (POP rst ... queue ...))]
    [(pattern fexps
       (acm ...)
       (atom rst ...)
       (queue ...))
     #'(pattern fexps
         (acm ... atom)
         (rst ...)
         (queue ...))]
    [(pattern fexps
       (acm ...)
       ()
       (POP queue ...))
     #'(pattern fexps
         (acm ... POP)
         (queue ...)
         ())]
    [(pattern fexps
       (acm ...)
       ()
       ())
     #'(finalize (fexps) (acm ...))]))

(define-syntax (clauses stx)
  (syntax-case stx (DONE)
    [(clauses (final ...) (expanded ...) ((pttrn body) rst ...))
     (syntax-case (local-expand #'(pattern ()
                                    ()
                                    (pttrn)
                                    ())
                                (syntax-local-context)
                                (list #'#%app))
                  ()
       ;  [((subpat ...) ...) #'(clauses () (expanded ...) (((subpat ...) body) ... rst ...))]
       [(pttrns ...) #'(clauses (final ... (pttrns body) ...) (expanded ...) (rst ...))])]
    [(clauses (final ...) () ()) #'(final ...)]))

(define-syntax (match/typed stx)
  (syntax-case stx ()
    [(match/typed tgt cls ...)
     (with-syntax ([(cls ...) (local-expand #'(clauses () () (cls ...)) (syntax-local-context) #f)])
       #'(match tgt
           cls ...))]))

(struct point ([x : Real] [y : Real]) #:transparent)
(struct breakpoint ([p1 : point] [p2 : point]) #:transparent)
(define-type tree (U node2 node3 point False))
(define-type oftree (U OF2 OF3 TI))
(define-type uftree (U UF TI))
(struct root
        ([cmp? : (-> breakpoint point Boolean)] [combine-keys : (-> breakpoint breakpoint breakpoint)]
                                                [t : tree]))
(struct node2 ([l : tree] [k : breakpoint] [r : tree]))
(struct node3 ([l : tree] [k1 : breakpoint] [m : tree] [k2 : breakpoint] [r : tree]))
(struct OF2 ([t1 : tree] [k : breakpoint] [t2 : tree]))
(struct OF3 ([t1 : tree] [k1 : breakpoint] [t2 : tree] [k2 : breakpoint] [t3 : tree]))
(struct UF ([t : tree]))
(struct TI ([t : tree]))
(: 23tree (-> (-> breakpoint point Boolean) (-> breakpoint breakpoint breakpoint) root))
(define (23tree cmp? combine-keys)
  (root cmp? combine-keys #f))

(define 23tree-empty?
  (match-lambda
    [(struct* root ([t root_node])) (not root_node)]))

(: height (-> tree Integer))
(define/match (height n)
  [((node2 l k r)) (+ 1 (height l))]
  [((node3 l k1 m k2 r)) (+ 1 (height l))]
  [(_) 0])

(define 23tree? root?)

(define-type balance-args
             (U (List oftree breakpoint tree)
                (List tree breakpoint oftree)
                (List oftree breakpoint tree breakpoint tree)
                (List tree breakpoint oftree breakpoint tree)
                (List tree breakpoint tree breakpoint oftree)))
(: balance
   (case-> [oftree breakpoint tree -> oftree]
           [tree breakpoint oftree -> oftree]
           [oftree breakpoint tree breakpoint tree -> oftree]
           [tree breakpoint oftree breakpoint tree -> oftree]
           [tree breakpoint tree breakpoint oftree -> oftree]))
(define balance
  (case-lambda
    [(l k r) (balance_ (list l k r))]
    [(l k1 m k2 r) (balance_ (list l k1 m k2 r))]))
(define (balance_ [rst : balance-args])
  :
  oftree
  (match rst
    [(list (struct TI (l)) k r) (TI (node2 l k r))]
    [(list l k (struct TI (r))) (TI (node2 l k r))]
    [(list (struct OF2 (l k1 m)) k2 r) (TI (node3 l k1 m k2 r))]
    [(list l k1 (struct OF2 (m k2 r))) (TI (node3 l k1 m k2 r))]
    [(list (struct OF3 (l k1 m1 k2 m2)) k3 r) (OF2 (node2 l k1 m1) k2 (node2 m2 k3 r))]
    [(list l k1 (struct OF3 (m1 k2 m2 k3 r))) (OF2 (node2 l k1 m1) k2 (node2 m2 k3 r))]
    ; node3
    [(list (struct TI (l)) k1 m k2 r) (TI (node3 l k1 m k2 r))]
    [(list l k1 (struct TI (m)) k2 r) (TI (node3 l k1 m k2 r))]
    [(list l k1 m k2 (struct TI (r))) (TI (node3 l k1 m k2 r))]
    [(list (struct OF2 (l1 k1 m1)) k2 m2 k3 r) (OF2 (node2 l1 k1 m1) k2 (node2 m2 k3 r))]
    [(list l1 k1 (struct OF2 (m1 k2 m2)) k3 r) (OF2 (node2 l1 k1 m1) k2 (node2 m2 k3 r))]
    [(list l1 k1 m1 k2 (struct OF2 (m2 k3 r))) (OF2 (node2 l1 k1 m1) k2 (node2 m2 k3 r))]
    [(list (struct OF3 (l1 k1 m1 k2 m2)) k3 m3 k4 r) (OF2 (node3 l1 k1 m1 k2 m2) k3 (node2 m3 k4 r))]
    [(list l1 k1 (struct OF3 (m1 k2 m2 k3 m3)) k4 r) (OF2 (node3 l1 k1 m1 k2 m2) k3 (node2 m3 k4 r))]
    [(list l1 k1 m1 k2 (struct OF3 (m2 k3 m3 k4 r)))
     (OF2 (node3 l1 k1 m1 k2 m2) k3 (node2 m3 k4 r))]))

(define-type balanced-args
             (U (List uftree breakpoint tree)
                (List tree breakpoint uftree)
                (List uftree breakpoint tree breakpoint tree)
                (List tree breakpoint uftree breakpoint tree)
                (List tree breakpoint tree breakpoint uftree)))
(: balance-d
   (case-> [uftree breakpoint tree -> uftree]
           [tree breakpoint uftree -> uftree]
           [uftree breakpoint tree breakpoint tree -> uftree]
           [tree breakpoint uftree breakpoint tree -> uftree]
           [tree breakpoint tree breakpoint uftree -> uftree]))
(define balance-d
  (case-lambda
    [(l k r) (balance-d_ (list l k r))]
    [(l k1 m k2 r) (balance-d_ (list l k1 m k2 r))]))
(define (balance-d_ [rst : balanced-args])
  :
  uftree
  (match/typed
   rst
   [(or (list (TI l) k r) (list l k (TI r))) (TI (node2 l k r))]
   [(or (list (UF l) k1 (node2 m k2 r)) (list (node2 l k1 m) k2 (UF r))) (UF (node3 l k1 m k2 r))]
   [(or (list (UF l) k1 (node3 m1 k2 m2 k3 r)) (list (node3 l k1 m1 k2 m2) k3 (UF r)))
    (TI (node2 (node2 l k1 m1) k2 (node2 m2 k3 r)))]
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

(struct cleft ([k : breakpoint]))
(struct cright ([k : breakpoint]))
(define-type combine-tree (Pairof (U #f cleft cright) uftree))
(define-type combine-args
             (U (List combine-tree breakpoint tree)
                (List tree breakpoint combine-tree)
                (List combine-tree breakpoint tree breakpoint tree)
                (List tree breakpoint combine-tree breakpoint tree)
                (List tree breakpoint tree breakpoint combine-tree)))
(define-type combine-type
             (case-> [combine-tree breakpoint tree -> combine-tree]
                     [tree breakpoint combine-tree -> combine-tree]
                     [combine-tree breakpoint tree breakpoint tree -> combine-tree]
                     [tree breakpoint combine-tree breakpoint tree -> combine-tree]
                     [tree breakpoint tree breakpoint combine-tree -> combine-tree]))
(: combine (-> (-> breakpoint breakpoint breakpoint) combine-type))
(define (combine combine-keys-balance)
  (case-lambda
    [(l k r) (combine_ combine-keys-balance (list l k r))]
    [(l k1 m k2 r) (combine_ combine-keys-balance (list l k1 m k2 r))]))
(define (combine_ [combine-keys-balance : (-> breakpoint breakpoint breakpoint)] [rst : combine-args])
  (match/typed
   rst
   [(or (list (cons #f l) k r) (list l k (cons #f r))) (cons #f (balance-d l k r))]
   [(list (cons (cright k_) l) k r) (cons #f (balance-d l (combine-keys-balance k_ k) r))]
   [(list l k (cons (cleft k_) r)) (cons #f (balance-d l (combine-keys-balance k k_) r))]
   [(or (list (cons op l) k r) (list l k (cons op r))) (cons op (balance-d l k r))]
   ; node3
   [(or (list (cons #f l) k1 m k2 r) (list l k1 (cons #f m) k2 r) (list l k1 m k2 (cons #f r)))
    (cons #f (balance-d l k1 m k2 r))]
   [(list (cons (cright k_) l) k1 m k2 r) (cons #f (balance-d l (combine-keys-balance k_ k1) m k2 r))]
   [(list l k1 (cons (cleft k_) m) k2 r) (cons #f (balance-d l (combine-keys-balance k1 k_) m k2 r))]
   [(list l k1 (cons (cright k_) m) k2 r) (cons #f (balance-d l k1 m (combine-keys-balance k_ k2) r))]
   [(list l k1 m k2 (cons (cleft k_) r)) (cons #f (balance-d l k1 m (combine-keys-balance k2 k_) r))]
   [(or (list (cons op l) k1 m k2 r) (list l k1 m k2 (cons op r)))
    (cons op (balance-d l k1 m k2 r))]))

(define (_23tree-split [t : tree] [v : point] [cmp? : (-> breakpoint point Boolean)])
  :
  oftree
  (match t
    [#f (TI v)]
    [(struct point _) (OF3 t (breakpoint t v) v (breakpoint v t) t)]
    [(struct node2 (l k r))
     (if (cmp? k v)
         (balance (_23tree-split l v cmp?) k r)
         (balance l k (_23tree-split r v cmp?)))]
    [(struct node3 (l k1 m k2 r))
     (cond
       [(cmp? k1 v) (balance (_23tree-split l v cmp?) k1 m k2 r)]
       [(cmp? k2 v) (balance l k1 (_23tree-split m v cmp?) k2 r)]
       [else (balance l k1 m k2 (_23tree-split r v cmp?))])]))

(define (23tree-inorder (t : root))
  (match-define (root cmp? _ root-node) t)
  (let rec
    :
    (Listof (U point breakpoint #f))
    ([node : tree root-node])
    (match node
      [(node2 l k r) (append (rec l) `(,k) (rec r))]
      [(node3 l k1 m k2 r) (append (rec l) `(,k1) (rec m) `(,k2) (rec r))]
      [(or (breakpoint _ _) (point _ _) #f) `(,node)])))

(define (_rightmost-val [t : tree])
  :
  (U point #f)
  (match t
    [(node2 l k r) (_rightmost-val r)]
    [(node3 l k1 m k2 r) (_rightmost-val r)]
    [(or #f (point _ _)) t]))

(define (_leftmost-val [t : tree])
  :
  (U point #f)
  (match t
    [(node2 l k r) (_leftmost-val l)]
    [(node3 l k1 m k2 r) (_leftmost-val l)]
    [(or #f (point _ _)) t]))

(define (_remove-leftmost-val [t : tree] [combine-inst : combine-type])
  :
  combine-tree
  (match t
    [(node2 l k r)
     (let ([l_ (_remove-leftmost-val l combine-inst)])
       (if l_
           (combine-inst (_remove-leftmost-val l combine-inst) k r)
           (cons (cleft k) (UF r))))]
    [(node3 l k1 m k2 r)
     (let ([l_ (_remove-leftmost-val l combine-inst)])
       (if l_
           (combine-inst (_remove-leftmost-val l combine-inst) k1 m k2 r)
           (cons (cleft k1) (TI node2 m k2 r))))]
    [val (cons #f (TI #f))]))

(define (_23tree-left-val [t : tree] [p : point] [cmp? : (-> breakpoint point Boolean)])
  :
  (U point #f)
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

(define (_23tree-right-val [t : tree] [p : point] [cmp? : (-> breakpoint point Boolean)])
  :
  (U point #f)
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

(define (_23tree-ref [t : tree] [p : point] [cmp? : (-> breakpoint point Boolean)])
  :
  (U point #f)
  (match t
    [(node2 l k r)
     (cond
       [(cmp? k p) (_23tree-ref l p cmp?)]
       [else (_23tree-ref r p cmp?)])]
    [(node3 l k1 m k2 r)
     (cond
       [(cmp? k1 p) (_23tree-ref l p cmp?)]
       [(cmp? k2 p) (_23tree-ref m p cmp?)]
       [else (_23tree-ref r p cmp?)])]
    [(or #f (point _ _)) t]))

(define (23tree-ref [t : root] [p : point] [y_ : (U Real #f) #f])
  (match/values (values t p y_)
                [((struct root (cmp? _ t)) p #f) (_23tree-ref t p cmp?)]
                [((struct root (cmp? _ t)) (point x _) (? number?))
                 (_23tree-ref t (point x y_) cmp?)]))
(define (23tree-left-val [t : root] [p : point] [y_ : (U Real #f) #f])
  (match/values (values t p y_)
                [((struct root (cmp? _ t)) p #f) (_23tree-left-val t p cmp?)]
                [((struct root (cmp? _ t)) (point x _) (? number?))
                 (_23tree-left-val t (point x y_) cmp?)]))
(define (23tree-right-val [t : root] [p : point] [y_ : (U Real #f) #f])
  (match/values (values t p y_)
                [((struct root (cmp? _ t)) p #f) (_23tree-right-val t p cmp?)]
                [((struct root (cmp? _ t)) (point x _) (? number?))
                 (_23tree-right-val t (point x y_) cmp?)]))

(define (arc->breakpoint [t : root] [p : point] [y_ : (U #f Real) #f])
  (let ([left (23tree-left-val t p y_)])
    (if left
        (breakpoint left p)
        'leftmost)))

(define (breakpoint->arc [t : root] [bp : breakpoint] [l : Real])
  :
  (U #f point)
  (define x (breakpoint->x bp l))
  (: cmp? (-> breakpoint point Boolean))
  (match-define (root cmp? _ #{t : tree}) t)
  (let fix ([t t]
            [bp bp]
            [l l])
    (match t
      [(node2 lt k rt)
       #:when (eq? bp 'leftmost)
       (_leftmost-val lt)]
      [(node2 lt (== bp) rt) (_leftmost-val rt)]
      [(node2 lt k rt)
       #:when (< x (breakpoint->x k l))
       (fix lt bp l)]
      [(node2 lt k rt) (fix rt bp l)]
      [(node3 lt k1 mt k2 rt)
       #:when (eq? bp 'leftmost)
       (_leftmost-val lt)]
      [(node3 lt (== bp) mt k2 rt) (_leftmost-val mt)]
      [(node3 lt k1 mt (== bp) rt) (_leftmost-val rt)]
      [(node3 lt k1 mt k2 rt)
       #:when (< x (breakpoint->x k1 l))
       (fix lt bp l)]
      [(node3 lt k1 mt k2 rt)
       #:when (< x (breakpoint->x k2 l))
       (fix mt bp l)]
      [(node3 lt k1 mt k2 rt) (fix rt bp l)])))

(define (_rightmost-key [t : tree])
  :
  (U #f breakpoint)
  (match t
    [(node2 l k r) (or (_rightmost-key r) k)]
    [(node3 l k1 m k2 r) (or (_rightmost-key r) k2)]
    [_ #f]))

(define (_leftmost-key [t : tree])
  :
  (U #f breakpoint)
  (match t
    [(node2 l k r) (or (_leftmost-key l) k)]
    [(node3 l k1 m k2 r) (or (_leftmost-key l) k1)]
    [_ #f]))

(define (_23tree-left-bp [t : tree] [bp : breakpoint] [l : Real])
  :
  (U #f breakpoint)
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

(define (23tree-left-bp [t : root] [bp : breakpoint] [l : Real])
  (match t
    [(root _ _ t) (_23tree-left-bp t bp l)]))

(define (_23tree-right-bp [t : tree] [bp : breakpoint] [l : Real])
  :
  (U #f breakpoint)
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

(define (23tree-right-bp [t : root] [bp : breakpoint] [l : Real])
  (match t
    [(root _ _ t) (_23tree-right-bp t bp l)]))

(: _23tree-remove
   (-> tree
       breakpoint
       Real
       (-> breakpoint point Boolean)
       (-> breakpoint breakpoint breakpoint)
       combine-tree))
(define (_23tree-remove t bp l cmp? combine-keys)
  (define combine-inst (combine combine-keys))
  (define x (breakpoint->x bp l))
  (match t
    [(node2 lt k rt)
     #:when (eq? bp 'leftmost)
     (let ([lt_ (_remove-leftmost-val lt combine-inst)])
       (if lt_
           (combine-inst lt_ k rt)
           (cons (cleft k) (UF rt))))]
    [(node2 lt (== bp) rt)

     (let ([rt_ (_remove-leftmost-val rt combine-inst)])
       (if rt_
           (combine-inst lt bp rt_)
           (cons (cright bp) (UF lt))))]
    [(node2 lt k rt)
     #:when (< x (breakpoint->x k l))
     (combine-inst (_23tree-remove lt bp l cmp? combine-keys) k rt)]
    [(node2 lt k rt) (combine-inst lt k (_23tree-remove rt bp l cmp? combine-keys))]
    [(node3 lt k1 mt k2 rt)
     #:when (eq? bp 'leftmost)
     (let ([lt_ (_remove-leftmost-val lt combine-inst)])
       (if lt_
           (combine-inst lt_ k1 mt k2 rt)
           (cons (cleft k1) (TI (node2 mt k2 rt)))))]
    [(node3 lt (== bp) mt k2 rt)
     (let ([mt_ (_remove-leftmost-val mt combine-inst)])
       (if mt_
           (combine-inst lt bp mt_ k2 rt)
           (cons #f (TI (node2 lt (combine-keys bp k2) rt)))))]
    [(node3 lt k1 mt (== bp) rt)
     (let ([rt_ (_remove-leftmost-val rt combine-inst)])
       (if rt_
           (combine-inst lt k1 mt bp rt_)
           (cons (cright bp) (TI (node2 lt bp mt)))))]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k1 l))
     (combine-inst (_23tree-remove lt bp l cmp? combine-keys) k1 mt k2 rt)]
    [(node3 lt k1 mt k2 rt)
     #:when (< x (breakpoint->x k2 l))
     (combine-inst lt k1 (_23tree-remove mt bp l cmp? combine-keys) k2 rt)]
    [(node3 lt k1 mt k2 rt) (combine-inst lt k1 mt k2 (_23tree-remove rt bp l cmp? combine-keys))]))

(: 23tree-split (-> root point root))
(define (23tree-split t v)
  (match-let ([(struct root (cmp? _ root-node)) t])
    (match (_23tree-split root-node v cmp?)
      [(TI root-node) (struct-copy root t [t root-node])]
      [(OF2 l k r) (struct-copy root t [t (node2 l k r)])]
      [(OF3 l k1 m k2 r) (struct-copy root t [t (node3 l k1 m k2 r)])])))

(: 23tree-remove (-> root breakpoint Real root))
(define (23tree-remove t bp l)
  (match (match/values (values t bp l)
                       [((root cmp? combine-keys t) bp l) (_23tree-remove t bp l cmp? combine-keys)])
    [(cons _ (or (UF root-node) (TI root-node))) (struct-copy root t [t root-node])]))

;; TODO ------------------------------------------

(define (breakpoint->xy [bp : breakpoint] [l : Real])
  :
  (Pairof Real Real)
  (match-let ([(breakpoint (point x1 y1) (point x2 y2)) bp])
    ; (printf "x1: ~v y1: ~v x2: ~v y2: ~v l: ~v\n" x1 y1 x2 y2 l)
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
    (let* ([f1
            :
            Real
            (/ 1 (* 2 (- y1 l)))]
           [f2
            :
            Real
            (/ 1 (* 2 (- y2 l)))]
           [r
            :
            Real
            (+ (* f2 (* y2 y2))
               (* f2 (* x2 x2))
               (- (* f1 (* y1 y1)))
               (- (* f1 (* x1 x1)))
               (* l l (- f1 f2)))]
           [a
            :
            Real
            (- f2 f1)]
           [b
            :
            Real
            (* 2 (- (* f1 x1) (* f2 x2)))]
           [c
            :
            Real
            r]
           [op -]
           [x
            :
            Real
            (assert (/ (op (- b) (sqrt (- (* b b) (* 4 a c)))) (* 2 a)) real?)]
           [y
            :
            Real
            (* f1 (+ (* x x) (- (* 2 x1 x)) (* y1 y1) (* x1 x1) (- (* l l))))])
      (cons x y))))

(define (arc->y [p : point] [x : Real] [l : Real])
  :
  Real
  (match-let ([(point x1 y1) p])
    (let* ([f1 (/ 1 (* 2 (- y1 l)))]
           [y (* f1 (+ (* x x) (- (* 2 x1 x)) (* y1 y1) (* x1 x1) (- (* l l))))])
      y)))

(define (breakpoint->x [bp : breakpoint] [l : Real])
  :
  Real
  (car (breakpoint->xy bp l)))
;; p is list of points

(define (cmp-bp-p [bp : breakpoint] [p : point] [l : Real])
  :
  Boolean
  (let ([bp-x (breakpoint->x bp l)]) (< (point-x p) bp-x)))

(define/match (breakpoint-merge l r)
  [((breakpoint l1 _) (breakpoint _ r2)) (breakpoint l1 r2)])
