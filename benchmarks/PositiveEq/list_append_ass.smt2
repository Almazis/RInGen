(set-logic HORN)

(declare-datatype Nat ((Z) (S (nextnat Nat))))
(declare-datatype Tree ((leaf) (node (trn1 Nat) (ltree Tree) (rtree Tree))))
(declare-datatype Lst ((nil) (cons (car Nat) (cdr Lst))))
(declare-datatype Lst2 ((nil2) (cons2 (car1 Nat) (car2 Nat) (cdr2 Lst2))))
(declare-datatype Queue ((queue (queue1 Lst) (queue2 Lst))))

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
(assert (forall ((x Nat)) (gt (S x) Z)))
(assert (forall ((x Nat) (y Nat)) (=> (gt x y) (gt (S x) (S y)))))
(assert (forall ((x Nat) (y Nat)) (=> (or (gt x y) (= x y)) (ge x y))))

(declare-fun len (Lst Nat) Bool)
(assert (len nil Z))
(assert (forall ((x Nat) (y Lst) (l Nat)) (=> (len y l) (len (cons x y) (S l)))))
(declare-fun qlen (Queue Nat) Bool)
(assert (forall ((x Lst) (y Lst) (xs Nat) (ys Nat) (s Nat)) (=> (and (len x xs) (len y ys) (add xs ys s)) (qlen (queue x y) s))))
(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((y Lst)) (append nil y y)))
(assert (forall ((c Nat) (x Lst) (y Lst) (z Lst)) (=> (append x y z) (append (cons c x) y (cons c z)))))

(assert (forall ((x Lst) (y Lst) (z Lst) (xy Lst) (yz Lst) (xyz1 Lst) (xyz2 Lst) (k Nat))
	(=> (and (append x y xy) (append y z yz) (append xy z xyz1) (append x yz xyz2) (= xyz1 (cons k xyz2))) false))) ;;


(check-sat)

