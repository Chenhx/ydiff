;; ydiff - a language-aware tool for comparing programs
;; Copyright (C) 2011-2013 Yin Wang (yinwang0@gmail.com)


;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

#lang racket

(require "structs.rkt")
(require "utils.rkt")


(provide (all-defined-out))


;-------------------------------------------------------------
;                      parameters
;-------------------------------------------------------------

;; The minimum size of a node to be considered as moved. Shouldn't be
;; too small, otherwise small deleted names may appear in a very
;; distant place!
(define *move-size* 5)


;; Similar to *move-size*, but this number is used for internal moves inside a
;; named body (for example a function). This number can be smaller than
;; *move-size*, usually set to 2 for maxmum accuracy without much noise.
(define *inner-move-size* 2)


;; Only memoize the diff of nodes of size larger than this number.
;; This effectively reduces memory usage.
(define *memo-node-size* 2)


;; Are we in moving phase?
;; This is internal switch used by the diff algorithm.
;; Do not modify by handl.
(define *moving* #f)



;;------------------ frames utils --------------------
(define deframe
  (lambda (node)
    (match node
      [(Node 'frame _ _ elts _ _)
       (apply append (map deframe elts))]
     [else (list node)])))


(define deframe-change
  (lambda (change)
    (cond
     [(ins? change)
      (apply append
             (map ins (deframe (Change-new change))))]
     [(del? change)
      (apply append
             (map del (deframe (Change-old change))))]
     [else (list change)])))


(define extract-frame
  (lambda (node1 node2 type)
    (match node1
      [(Node type1 start1 end1 elts1 size ctx)
       (let ([frame-elts (filter (lambda (x)
                                   (not (eq? x node2)))
                                 elts1)])
         (type (Node 'frame start1 start1 frame-elts (- size (node-size node2)) ctx)))]
      [_ fatal 'extract-frame "I only accept Node"])))


;; (define n1 (Token "ok" 0 1))
;; (define n2 (Expr 'ok 0 2 (list n1 (Token "bar" 1 2))))
;; (map deframe-change (extract-frame n2 n1 ins))



;-------------------------------------------------------------
;                       diff proper
;-------------------------------------------------------------

; 2-D memoization table
(define make-table
  (lambda (dim1 dim2)
    (let ([vec (make-vector (add1 dim1))])
      (let loop ([n 0])
        (cond
         [(= n (vector-length vec)) vec]
         [else
          (vector-set! vec n (make-vector (add1 dim2) #f))
          (loop (add1 n))])))))


(define table-ref
  (lambda (t x y)
    (let ([row (vector-ref t x)])
      (vector-ref row y))))


(define table-set!
  (lambda (t x y v)
    (let ([row (vector-ref t x)])
      (vector-set! row y v))))



;---------------- string distance function -----------------

;; string distance is no longer used because string=? saffice to
;; compare strings in ASTs. Retain it here for possible later uses.
(define string-dist
  (lambda (s1 s2)
    (let* ([len1 (string-length s1)]
           [len2 (string-length s2)]
           [t (make-table len1 len2)]
           [char-dist (dist1 t s1 0 s2 0)])
      (cond
       [(= 0 (+ len1 len2)) 0]
       [else
        (/ (* 2.0 char-dist) (+ len1 len2))]))))


(define dist1
  (lambda (table s1 start1 s2 start2)
    (define memo
      (lambda (value)
        (table-set! table start1 start2 value)
        value))
    (cond
     [(table-ref table start1 start2)
      => (lambda (cached) cached)]
     [(= start1 (string-length s1))
      (memo (- (string-length s2) start2))]
     [(= start2 (string-length s2))
      (memo (- (string-length s1) start1))]
     [else
      (let* ([c1 (string-ref s1 start1)]
             [c2 (string-ref s2 start2)]
             [d0 (cond
                  [(char=? c1 c2) 0]
                  [(char=? (char-downcase c1)
                           (char-downcase c2)) 1]
                  [else 2])]
             [d1 (+ d0 (dist1 table s1 (add1 start1) s2 (add1 start2)))]
             [d2 (+ 1 (dist1 table s1 (add1 start1) s2 start2))]
             [d3 (+ 1 (dist1 table s1 start1 s2 (add1 start2)))])
        (memo (min d1 d2 d3)))])))



;--------------------- the primary diff function -------------------

(define get-cost
  (lambda (changes)
    (apply + (map Change-cost changes))))


;; global 2-D hash for storing known diffs
(define *diff-hash* (make-hasheq))

(define diff-node
  (lambda (node1 node2)

    (define memo
      (lambda (v)
        (and (> (node-size node1) *memo-node-size*)
             (> (node-size node2) *memo-node-size*)
             (hash-put! *diff-hash* node1 node2 v))
        v))

    (define try-extract
      (lambda (changes)
        (let ([cost (get-cost changes)])
         (cond
          [(or (not *moving*)
               (zero? cost))
           (memo changes)]
          [else
           (let ([m (diff-extract node1 node2)])
             (cond
              [(not m)
               (memo changes)]
              [else
               (memo m)]))]))))


    (diff-progress 1) ;; progress bar

    (cond
     [(hash-get *diff-hash* node1 node2)
      => (lambda (x) x)]
     [(and (character? node1) (character? node2))
      (diff-string (char->string (Node-elts node1))
                   (char->string (Node-elts node2))
                   node1 node2)]
     [(and (str? node1) (str? node2))
      (diff-string (Node-elts node1) (Node-elts node2) node1 node2)]
     [(and (comment? node1) (comment? node2))
      (diff-string (Node-elts node1) (Node-elts node2) node1 node2)]
     [(and (token? node1) (token? node2))
      (diff-string (Node-elts node1) (Node-elts node2) node1 node2)]
     [(and (Node? node1) (Node? node2)
           (eq? (get-type node1) (get-type node2)))
      (let ([m (diff-list (Node-elts node1) (Node-elts node2))])
        (try-extract m))]
     [(and (pair? node1) (not (pair? node2)))
      (diff-list node1 (list node2))]
     [(and (not (pair? node1)) (pair? node2))
      (diff-list (list node1) node2)]
     [(and (pair? node1) (pair? node2))
      (diff-list node1 node2)]
     [else
      (let ([m (total node1 node2)])
        (try-extract m))])))




;; helper for nodes with string contents (Str, Comment, Token etc.)
(define diff-string
  (lambda (string1 string2 node1 node2)
    (cond
     [(string=? string1 string2)
      (mov node1 node2 0)]
     [else
      (total node1 node2)])))


(define diff-list
  (lambda (ls1 ls2)
    (let ([ls1 (sort ls1 node-sort-fn)]
          [ls2 (sort ls2 node-sort-fn)])
      (diff-list1 (make-hasheq) ls1 ls2))))


(define diff-list1
  (lambda (table ls1 ls2)

    (define memo
      (lambda (v)
        (hash-put! table ls1 ls2 v)
        v))

    (define guess
      (lambda (ls1  ls2)
        (let* ([m0 (diff-node (car ls1) (car ls2))]
               [m1 (diff-list1 table (cdr ls1) (cdr ls2))]
               [c0 (get-cost m0)]
               [c1 (get-cost m1)])
          (cond
           [(or (zero? c0)
                (same-def? (car ls1) (car ls2)))
            (memo (append m0 m1))]
           [else
            (let* ([m2 (diff-list1 table (cdr ls1) ls2 )]
                   [m3 (diff-list1 table ls1 (cdr ls2))]
                   [cost2 (+ (get-cost m2) (node-size (car ls1)))]
                   [cost3 (+ (get-cost m3) (node-size (car ls2)))])
              (cond
               [(<= cost2 cost3)
                (memo (append (del (car ls1)) m2))]
               [else
                (memo (append (ins (car ls2)) m3))]))]))))

    (cond
     [(hash-get table ls1 ls2)
      => (lambda (x) x)]
     [(and (null? ls1) (null? ls2))
      '()]
     [(null? ls1)
      (apply append (map ins ls2))]
     [(null? ls2)
      (apply append (map del ls1))]
     [else
      (guess ls1 ls2)])))



(define same-ctx?
  (lambda (x y)
    (and (Node? x)
         (Node? y)
         (Node-ctx x)
         (Node-ctx y)
         (>= (node-size x) *inner-move-size*)
         (>= (node-size y) *inner-move-size*)
         (eq? (Node-ctx x) (Node-ctx y)))))


;; structure extraction
(define diff-extract
  (lambda (node1 node2)
    (cond
     [(and (Node? node1) (Node? node2)
           (and (big-node? node1)
                (big-node? node2)))
      (cond
       [(<= (node-size node1) (node-size node2))
        (let loop ([elts2 (Node-elts node2)])
          (cond
           [(pair? elts2)
            (let ([m0 (diff-node node1 (car elts2))])
              (cond
               [(or (same-def? node1 (car elts2))
                    (and (zero? (get-cost m0))
                         (big-node? node1)))
                (let ([frame (extract-frame node2 (car elts2) ins0)])
                  (append m0 frame))]
               [else
                (loop (cdr elts2))]))]
           [else #f]))]
       [else
        (let loop ([elts1 (Node-elts node1)])
          (cond
           [(pair? elts1)
            (let ([m0 (diff-node (car elts1) node2)])
              (cond
               [(or (same-def? (car elts1) node2)
                    (and (zero? (get-cost m0))
                         (big-node? node2)))
                (let ([frame (extract-frame node1 (car elts1) del0)])
                  (append m0 frame))]
               [else
                (loop (cdr elts1))]))]
           [else #f]))])]
     [else #f])))



;-------------------------------------------------------------
;                    finding moves
;-------------------------------------------------------------

(define big-node?
  (lambda (node)
    (>= (node-size node) *move-size*)))


(define big-change?
  (lambda (c)
    (cond
     [(ins? c)
      (big-node? (Change-new c))]
     [(del? c)
      (big-node? (Change-old c))]
     [(mov? c)
      (or (big-node? (Change-old c))
          (big-node? (Change-new c)))])))


(define node-sort-fn
  (lambda (x y)
    (let ([name1 (get-name x)]
          [name2 (get-name y)])
      (cond
       [(and name1 name2)
        (string<? (symbol->string name1)
                  (symbol->string name2))]
       [(and name1 (not name2)) #t]
       [(and (not name1) name2) #f]
       [else
        (< (Node-start x) (Node-start y))]))))



;; iterate diff-list on the list of changes
(define find-moves
  (lambda (changes)
    (set! *moving* #t)
    (set! *diff-hash* (make-hasheq))
    (let loop ([workset changes]
               [finished '()])
      (diff-progress "|")
      (let* ([dels (filter (predand del? big-change?) workset)]
             [adds (filter (predand ins? big-change?) workset)]
             [rest (set- workset (append dels adds))]
             [ls1 (sort (map Change-old dels) node-sort-fn)]
             [ls2 (sort (map Change-new adds) node-sort-fn)]
             [m (diff-list ls1 ls2)]
             [new-moves (filter mov? m)])
        (cond
         [(null? new-moves)
          (let ([all-changes (append workset finished)])
            (apply append (map deframe-change all-changes)))]
         [else
          (let ([new-changes (filter (negate mov?) m)])
            (loop new-changes
                  (append new-moves rest finished)))])))))


;; poor man's progress bar
(define diff-progress
  (new-progress 10000))


(define cleanup
  (lambda ()
    (set! *diff-hash* #f)))


;; main diff function
;; returns all changes after diffing and moving
(define diff
  (lambda (node1 node2)
    (letv ([start (current-seconds)]    ; start timer
           [size1 (node-size node1)]
           [size2 (node-size node2)])

      (printf "[info] size of program 1: ~a~n" size1)
      (printf "[info] size of program 2: ~a~n" size2)

      (set-node-context node1 'top)
      (set-node-context node2 'top)

      (printf "[diffing]~n")

      (let* ([changes (diff-node node1 node2)]
             [cost (get-cost changes)])
        (diff-progress 'reset)
        (printf "~n[moving]~n")
        (let ([changes (find-moves changes)]
              [end (current-seconds)])
          (printf "~n[finished] ~a seconds~n" (- end start))
          (printf "~n[info] count: ~a~n" (diff-progress 'get))
          (cleanup)
          changes)))))
