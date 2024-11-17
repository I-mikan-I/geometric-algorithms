#lang racket
(require scapegoat-tree)
(require (prefix-in bh: pfds/heap/binomial))
(require data/order)
;(require (submod "utils.rkt" no-contract))
(require "utils.rkt")
(require "utils/vtree.rkt")

(provide (all-defined-out))

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

(struct circle (x y bp [removed #:auto #:mutable]) #:auto-value #f #:transparent)
(define (circle-center p1 p2 p3)
  (printf "p1: ~a, p2: ~a, p3: ~a\n" p1 p2 p3)
  (match-let ([(point x1 y1) p1]
              [(point x2 y2) p2]
              [(point x3 y3) p3])
    (let* ([s1 (+ (* x1 x1) (* y1 y1))]
           [s2 (+ (* x2 x2) (* y2 y2))]
           [s3 (+ (* x3 x3) (* y3 y3))]
           [b (+ (* s1 (- y2 y3)) (* s2 (- y3 y1)) (* s3 (- y1 y2)))]
           [a (+ (* x1 (- y2 y3)) (- (* y1 (- x2 x3))) (* x2 y3) (- (* x3 y2)))]
           [c (+ (* s1 (- x3 x2)) (* s2 (- x1 x3)) (* s3 (- x2 x1)))])
      (if (equal? a 0)
          (point 0 +inf.0)
          (let* ([x (/ b (* 2 a))]
                 [y (/ c (* 2 a))]
                 [r (sqrt (+ (* (- x x1) (- x x1)) (* (- y y1) (- y y1))))])
            (if (>= (- y r) (min y1 y2 y3))
                (point 0 +inf.0)
                (point x (- y r))))))))

; points define arcs at the leafs of our 2-3 tree.
; we need to map circle event -> arc
;   can be done via breakpoint: breakpoints are unique
; we need to map arc -> circle event
;   can also be done via pointer
; arc uniquely defined by left breakpoint
; have to query: breakpoint -> arc, arc -> left arc/right arc

(define (close-graph graph_ bp_node_map l)
  (define graph
    (for/fold ([graph graph_]) ([(k v) (in-dict bp_node_map)])
      (let* ([new-node (breakpoint->xy k l)]
             [graph (dict-update graph v (lambda (adj-list) (cons new-node adj-list)))])
        (dict-set graph new-node (list v)))))
  graph)

(define (voronoi . p_)
  (define (bp-cmp bp site)
    (cmp-bp-p bp site (point-y site)))
  (define combine-keys breakpoint-merge)
  (define p (map (lambda (p) (point (car p) (cdr p))) p_))
  (define queue
    (apply bh:heap
           (lambda (p1 p2)
             ((match p1
                [(point _ y) y]
                [(circle _ y _ _) y])
              . > .
              (match p2
                [(point _ y) y]
                [(circle _ y _ _) y])))
           p))
  (define tree (23tree bp-cmp combine-keys))
  (define arc_ce_map (hash))
  (define bp_node_map (hash))
  (define graph (hash)) ; adjacency lists
  (define (event p tree queue arc_ce_map graph bp_node_map)
    (match p
      [(point x y) ; site event
       (if (23tree-empty? tree)
           (values (23tree-split tree p) queue arc_ce_map graph bp_node_map)
           (let* ([m (23tree-ref tree p)]
                  [m-bp (arc->breakpoint tree m y)]
                  [m-ce (dict-ref arc_ce_map m-bp #f)]
                  [l (23tree-left-val tree m y)]
                  [r (23tree-right-val tree m y)])
             (begin
               (printf "m-bp: ~v\n" m-bp)
               (if m-ce
                   ((begin
                      (printf "removed circle ~v\n" m-ce)
                      (set-circle-removed! m-ce #t)))
                   (void))
               (let ([tree (23tree-split tree p)])
                 ;; get both new breakpoints, create new node starting edge.
                 ;; associate node to both breakpoints
                 ;; on circle event, create final node ending edge. and connect in adjacency list
                 (let* ([bp-node (cons (point-x p) (arc->y m (point-x p) (point-y p)))]
                        [graph (dict-set graph bp-node '())]
                        [bp_node_map
                         (dict-set* bp_node_map (breakpoint m p) bp-node (breakpoint p m) bp-node)]
                        [left-ce (if (point? l)
                                     (match-let ([(point cx cy) (circle-center l m p)])
                                       (if (< cy y)
                                           (circle cx cy (breakpoint l m))
                                           #f))
                                     #f)]
                        [right-ce (if (point? r)
                                      (match-let ([(point cx cy) (circle-center p m r)])
                                        (if (< cy y)
                                            (circle cx cy (breakpoint p m))
                                            #f))
                                      #f)]
                        [arc_ce_map (dict-remove arc_ce_map m-bp)]
                        [arc_ce_map (if left-ce
                                        (dict-set arc_ce_map (circle-bp left-ce) left-ce)
                                        arc_ce_map)]
                        [arc_ce_map (if right-ce
                                        (dict-set arc_ce_map (circle-bp right-ce) right-ce)
                                        arc_ce_map)]
                        [queue (if left-ce
                                   (begin
                                     (printf "inserted ce: ~v\n" left-ce)
                                     (bh:insert left-ce queue))
                                   queue)]
                        [queue (if right-ce
                                   (begin
                                     (printf "inserted ce: ~v\n" right-ce)
                                     (bh:insert right-ce queue))
                                   queue)])
                   (values tree queue arc_ce_map graph bp_node_map))))))]
      [(circle x y (and (breakpoint l p) bp) #f) ; circle event
       (printf "circle event y = ~v\n" y)
       (let* ([lbp (23tree-left-bp tree bp y)]
              [rbp (23tree-right-bp tree bp y)]
              [node-left (dict-ref bp_node_map bp)]
              [node-right (dict-ref bp_node_map rbp)]
              [new-node (breakpoint->xy bp y)]
              [graph (dict-set graph new-node (list node-left node-right))]
              [graph (foldl (lambda (key graph)
                              (dict-update graph key (lambda (adj_list) (cons new-node adj_list))))
                            graph
                            (list node-left node-right))]
              [bp_node_map (dict-remove (dict-remove bp_node_map rbp) bp)]
              [l-ce (dict-ref arc_ce_map lbp #f)]
              [r-ce (dict-ref arc_ce_map rbp #f)]
              [ll (if (breakpoint? lbp)
                      (breakpoint-p1 lbp)
                      #f)]
              [r (if (breakpoint? rbp)
                     (breakpoint-p2 rbp)
                     #f)]
              [rr (if r
                      (23tree-right-val tree r y)
                      #f)]
              [bp_node_map (dict-set bp_node_map (breakpoint l r) new-node)]
              [left-ce (if (and (point? ll) (point? l) (point? r))
                           (match-let ([(point cx cy) (circle-center ll l r)])
                             (if (< cy y)
                                 (circle cx cy (breakpoint ll l))
                                 #f))
                           #f)]
              [right-ce (if (and (point? l) (point? r) (point? rr))
                            (match-let ([(point cx cy) (circle-center l r rr)])
                              (if (< cy y)
                                  (circle cx cy (breakpoint l r))
                                  #f))
                            #f)]
              [arc_ce_map (dict-remove arc_ce_map lbp)]
              [arc_ce_map (dict-remove arc_ce_map rbp)]
              [arc_ce_map (dict-remove arc_ce_map bp)]
              [arc_ce_map (if left-ce
                              (dict-set arc_ce_map (circle-bp left-ce) left-ce)
                              arc_ce_map)]
              [arc_ce_map (if right-ce
                              (dict-set arc_ce_map (circle-bp right-ce) right-ce)
                              arc_ce_map)]
              [queue (if left-ce
                         (bh:insert left-ce queue)
                         queue)]
              [queue (if right-ce
                         (bh:insert right-ce queue)
                         queue)]
              [tree (23tree-remove tree bp y)])
         (begin
           (printf "lbp: ~v, rbp: ~v, bp: ~v, l: ~v, r: ~v, p: ~v, ll: ~v, rr: ~v\n"
                   lbp
                   rbp
                   bp
                   l
                   r
                   p
                   ll
                   rr)
           (if l-ce
               (set-circle-removed! l-ce #t)
               (void))
           (if r-ce
               (set-circle-removed! r-ce #t)
               (void))
           (values tree queue arc_ce_map graph bp_node_map)))]
      ; removed event
      [_ (values tree queue arc_ce_map)]))
  (let while ([tree tree]
              [queue queue]
              [arc_ce_map arc_ce_map]
              [graph graph]
              [bp_node_map bp_node_map]
              [y_min 0])

    (printf "while inorder: ~v\n" (23tree-inorder tree))
    (printf "map ~v\n" (dict->list arc_ce_map))
    (cond
      [(bh:empty? queue) (close-graph graph bp_node_map (- y_min 10))]
      [else
       (let*-values ([(next-event) (bh:find-min/max queue)]
                     [(y_min) (if (point? next-event)
                                  (point-y next-event)
                                  (circle-y next-event))]
                     [(queue) (bh:delete-min/max queue)]
                     [(tree queue arc_ce_map graph bp_node_map)
                      (event next-event tree queue arc_ce_map graph bp_node_map)])
         (while tree queue arc_ce_map graph bp_node_map y_min))])))

(module+ test-tree
  (require plot)

  (plot-new-window? #t)
  (define t (23tree (lambda (bp p) (cmp-bp-p bp p (point-y p))) breakpoint-merge))
  (define ps (list (point 5 14) (point 15 12) (point 25 10) (point 13 9)))
  (set! t
        (for/fold ([t t]) ([p ps])
          (printf "inorder: ~v\n" (23tree-inorder t))
          (23tree-split t p)))

  (define/match (arc p l)
    ; y = (1/2(y1 - l)) * (x^2 -2x1*x + y1^2 + x1^2 -l^2)
    [((point x1 y1) l)
     (lambda (x)
       (* (/ 1 (* 2 (- y1 l))) (+ (* x x) (- (* 2 x1 x)) (* x1 x1) (* y1 y1) (- (* l l)))))])
  ; (plot (map (lambda (p) (function (arc p 0) 0 200 #:y-min -50 #:y-max 400)) points))
  (printf "inorder: ~v\n" (23tree-inorder t))
  (define ref1 (23tree-ref t (point 11 5)))
  (printf "get-ref ~v ~v\n" (point 11 5) ref1)
  (printf "get-left ~v\n" (23tree-left-val t (point 11 8.99)))
  (printf "get-right ~v\n" (23tree-right-val t (point 11 8.99)))

  (define graph (voronoi (cons 5 14) (cons 15 12) (cons 25 10) (cons 13 9)))
  (define pl_lines
    (for*/list ([(n v) (in-dict graph)]
                [n2 v])
      (lines `((,(car n) ,(cdr n)) (,(car n2) ,(cdr n2))))))
  (printf "\nfinal graph: ~v\n" graph)
  (plot (cons (points (map (lambda (p) (list (point-x p) (point-y p))) ps)) pl_lines)))

(module+ test
  (define data '((0 . 1) (5 . 1) (8 . 1) (100 . 1) (101 . 1) (-20 . 1)))
  (apply scanline data)
  (set! data '((0 . 1) (5 . 3) (8 . 5) (100 . 100) (101 . 23) (-20 . -2) (-19 . -10)))
  (apply scanline data))
