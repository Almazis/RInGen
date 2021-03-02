(set-logic HORN)

(declare-datatype Nat ((Z) (S (nextnat Nat))))
(declare-fun add (Nat Nat Nat) Bool)
(declare-fun lt (Nat Nat) Bool)
(declare-fun le (Nat Nat) Bool)
(declare-fun gt (Nat Nat) Bool)
(declare-fun ge (Nat Nat) Bool)
(assert (forall ((y Nat)) (add Z y y)))
(assert (forall ((x Nat) (y Nat) (z Nat)) (=> (add x y z) (add (S x) y (S z)))))
(assert (forall ((y Nat)) (lt Z (S y))))
(assert (forall ((x Nat) (y Nat)) (=> (lt x y) (lt (S x) (S y)))))
(assert (forall ((x Nat) (y Nat)) (=> (or (lt x y) (= x y)) (le x y))))
(assert (forall ((x Nat) (y Nat)) (=> (lt y x) (gt x y))))
(assert (forall ((x Nat) (y Nat)) (=> (le y x) (ge x y))))
(declare-fun diseqNat (Nat Nat) Bool)
(assert (forall ((x Nat)) (diseqNat Z (S x))))
(assert (forall ((x Nat)) (diseqNat (S x) Z)))
(assert (forall ((x Nat) (y Nat)) (=> (diseqNat x y) (diseqNat (S x) (S y)))))
(declare-datatype Lst ((nil) (cons (car Nat) (cdr Lst))))
(declare-fun diseqLst (Lst Lst) Bool)
(assert (forall ((c Nat) (x Lst)) (diseqLst nil (cons c x))))
(assert (forall ((c Nat) (x Lst)) (diseqLst (cons c x) nil)))
(assert (forall ((c1 Nat) (c2 Nat) (x Lst) (y Lst)) (=> (diseqNat c1 c2) (diseqLst (cons c1 x) (cons c2 y)))))
(assert (forall ((c1 Nat) (c2 Nat) (x Lst) (y Lst)) (=> (diseqLst x y) (diseqLst (cons c1 x) (cons c2 y)))))


(declare-fun count (Nat Lst Nat) Bool)
(declare-fun incorrect () Bool)
(declare-fun rev (Lst Lst) Bool)
(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((A Nat) (B Lst) (C Nat))
  (=> (and (= C Z) (= B nil)) (count A B C))))
(assert (forall ((A Lst) (B Nat) (C Nat) (D Lst) (E Nat))
  (=> (and (count C A B) (= D (cons C A)) (= E (S B)) (ge B Z))
      (count C D E))))
(assert (forall ((A Nat) (B Lst) (C Nat) (D Lst) (E Nat))
  (=> (and (count C B E) (= D (cons A B)) (diseqNat C A) (ge E Z))
      (count C D E))))
(assert (forall ((A Lst) (B Lst)) (=> (= A nil) (append A B B))))
(assert (forall ((A Nat)
         (B Lst)
         (C Lst)
         (D Lst)
         (E Lst)
         (F Lst))
  (=> (and (append B E C) (= F (cons A C)) (= D (cons A B))) (append D E F))))
(assert (forall ((A Lst) (B Lst))
  (=> (and (= B nil) (= A nil)) (rev A B))))
(assert (forall ((A Nat)
         (B Lst)
         (C Lst)
         (D Lst)
         (E Lst)
         (F Lst))
  (=> (and (append C D F) (rev B C) (= D (cons A nil)) (= E (cons A B)))
      (rev E F))))
(assert (forall ((A Nat) (B Lst) (C Nat) (D Lst) (E Nat))
  (=> (and (count C D E)
           (count C B A)
           (rev B D)
           (ge E Z)
           (diseqNat A E)
           (ge A Z))
      incorrect)))
(assert (=> incorrect false))
(check-sat)

