(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(define-fun-rec
  risers
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y z)
      (match z
        ((nil2 (cons (cons2 y nil2) nil))
         ((cons2 y2 xs)
          (ite
            (<= y y2)
            (match (risers (cons2 y2 xs))
              ((nil nil)
               ((cons ys yss) (cons (cons2 y ys) yss))))
            (cons (cons2 y nil2) (risers (cons2 y2 xs)))))))))))
(define-fun-rec
  lmerge
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z x2)
      (match y
        ((nil2 (cons2 z x2))
         ((cons2 x3 x4)
          (ite
            (<= z x3) (cons2 z (lmerge x2 (cons2 x3 x4)))
            (cons2 x3 (lmerge (cons2 z x2) x4))))))))))
(define-fun-rec
  pairwise
  ((x list)) list
  (match x
    ((nil nil)
     ((cons xs y)
      (match y
        ((nil (cons xs nil))
         ((cons ys xss) (cons (lmerge xs ys) (pairwise xss)))))))))
(define-fun-rec
  mergingbu2
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons xs y)
      (match y
        ((nil xs)
         ((cons z x2) (mergingbu2 (pairwise (cons xs (cons z x2)))))))))))
(define-fun
  msortbu2
  ((x list2)) list2 (mergingbu2 (risers x)))
(define-fun-rec
  insert2
  ((x Int) (y list2)) list2
  (match y
    ((nil2 (cons2 x nil2))
     ((cons2 z xs)
      (ite (<= x z) (cons2 x (cons2 z xs)) (cons2 z (insert2 x xs)))))))
(define-fun-rec
  isort
  ((x list2)) list2
  (match x
    ((nil2 nil2)
     ((cons2 y xs) (insert2 y (isort xs))))))
(assert (not (forall ((xs list2)) (= (msortbu2 xs) (isort xs)))))
(check-sat)
