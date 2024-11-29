#lang racket

(require racket/gui/base)
(require racket/draw)
(require "lib.rkt")

(define voronoi-canvas%
  (class canvas%
    (field [points '()]
           [lines '()])
    (define/override (on-event event)
      (if (equal? (send event get-event-type) 'left-up)
          (let ([x (send event get-x)]
                [y (send event get-y)])
            (set! points (cons `(,x . ,y) points))
            (print points)
            (define graph (apply voronoi points))
            (set! lines
                  (for*/list ([(n v) (in-dict graph)]
                              [n2 v])
                    (vector-immutable (car n) (cdr n) (car n2) (cdr n2))))
            (send this on-paint))
          (void)))
    (super-new)))

(define frame (new frame% [label "Example"] [width 600] [height 600]))
(new voronoi-canvas%
     [parent frame]
     [paint-callback
      (lambda (canvas dc)
        (for ([p (get-field points canvas)])
          (send dc draw-ellipse (car p) (cdr p) 5 5))
        (for ([vec (get-field lines canvas)])
          (send dc
                draw-line
                (vector-ref vec 0)
                (vector-ref vec 1)
                (vector-ref vec 2)
                (vector-ref vec 3))))])
(send frame show #t)
