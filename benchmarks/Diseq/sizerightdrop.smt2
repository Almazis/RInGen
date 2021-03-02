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
(declare-datatype Tree ((leaf) (node (trn1 Nat) (ltree Tree) (rtree Tree))))


(declare-fun rightdrop (Nat Tree Tree) Bool)
(declare-fun size (Tree Nat) Bool)
(declare-fun incorrect () Bool)
(declare-fun nmax (Nat Nat Nat) Bool)
(declare-fun height (Tree Nat) Bool)
(assert (forall ((A Nat) (B Nat)) (=> (le (S A) B) (nmax A B B))))
(assert (forall ((A Nat) (B Nat)) (=> (ge B A) (nmax B A B))))
(assert (forall ((A Nat) (B Tree) (C Tree))
  (=> (and (= C leaf) (= B leaf)) (rightdrop A B C))))
(assert (forall ((A Nat)
         (B Tree)
         (C Tree)
         (D Nat)
         (E Tree)
         (F Tree))
  (=> (and (= E (node A B C)) (le D Z) (= F (node A B C))) (rightdrop D E F))))
(assert (forall ((A Nat)
         (B Tree)
         (C Nat)
         (D Tree)
         (E Nat)
         (F Tree)
         (G Tree))
  (=> (and (rightdrop C D G) (= F (node A B D)) (= E (S C)) (gt E Z))
      (rightdrop E F G))))
(assert (forall ((A Tree) (B Nat)) (=> (and (= B Z) (= A leaf)) (height A B))))
(assert (forall ((A Nat)
         (B Tree)
         (C Nat)
         (D Nat)
         (E Tree)
         (F Nat)
         (G Tree)
         (H Nat))
  (=> (and (height E F)
           (height B C)
           (nmax C F D)
           (= H (S D))
           (= G (node A B E)))
      (height G H))))
(assert (forall ((A Tree) (B Nat)) (=> (and (= B Z) (= A leaf)) (size A B))))
(assert (forall ((A Nat)
         (B Tree)
         (C Nat)
         (D Tree)
         (E Nat)
         (F Tree)
         (G Nat))
  (=> (and (size D E) (size B C) (= F (node A B D)) (add (S E) C G)) (size F G))))
(assert (forall ((A Tree) (B Tree) (C Nat))
  (=> (and (size B C) (height A (S (S Z))) (size A (S (S (S Z)))) (rightdrop (S Z) A B) (diseqNat C (S Z)))
      incorrect)))
(assert (=> incorrect false))
(check-sat)

