(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_1 ) (Z_2 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_33 Nat_0))
	(unS_1 x_33 (Z_2 x_33))))
(assert (isZ_2 Z_1))
(assert (forall ((x_35 Nat_0))
	(isZ_3 (Z_2 x_35))))
(assert (forall ((x_36 Nat_0))
	(diseqNat_0 Z_1 (Z_2 x_36))))
(assert (forall ((x_37 Nat_0))
	(diseqNat_0 (Z_2 x_37) Z_1)))
(assert (forall ((x_38 Nat_0) (x_39 Nat_0))
	(=> (diseqNat_0 x_38 x_39)
	    (diseqNat_0 (Z_2 x_38) (Z_2 x_39)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_3 Nat_0))
	(add_0 y_3 Z_1 y_3)))
(assert (forall ((r_0 Nat_0) (x_17 Nat_0) (y_3 Nat_0))
	(=> (add_0 r_0 x_17 y_3)
	    (add_0 (Z_2 r_0) (Z_2 x_17) y_3))))
(assert (forall ((y_3 Nat_0))
	(minus_0 Z_1 Z_1 y_3)))
(assert (forall ((r_0 Nat_0) (x_17 Nat_0) (y_3 Nat_0))
	(=> (minus_0 r_0 x_17 y_3)
	    (minus_0 (Z_2 r_0) (Z_2 x_17) y_3))))
(assert (forall ((y_3 Nat_0))
	(le_0 Z_1 y_3)))
(assert (forall ((x_17 Nat_0) (y_3 Nat_0))
	(=> (le_0 x_17 y_3)
	    (le_0 (Z_2 x_17) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(ge_0 y_3 Z_1)))
(assert (forall ((x_17 Nat_0) (y_3 Nat_0))
	(=> (ge_0 x_17 y_3)
	    (ge_0 (Z_2 x_17) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(lt_0 Z_1 (Z_2 y_3))))
(assert (forall ((x_17 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_17 y_3)
	    (lt_0 (Z_2 x_17) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(gt_0 (Z_2 y_3) Z_1)))
(assert (forall ((x_17 Nat_0) (y_3 Nat_0))
	(=> (gt_0 x_17 y_3)
	    (gt_0 (Z_2 x_17) (Z_2 y_3)))))
(assert (forall ((y_3 Nat_0))
	(mult_0 Z_1 Z_1 y_3)))
(assert (forall ((r_0 Nat_0) (x_17 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (mult_0 r_0 x_17 y_3)
			(add_0 z_3 r_0 y_3))
		(mult_0 z_3 (Z_2 x_17) y_3))))
(assert (forall ((x_17 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_17 y_3)
	    (div_0 Z_1 x_17 y_3))))
(assert (forall ((r_0 Nat_0) (x_17 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_17 y_3)
			(minus_0 z_3 x_17 y_3)
			(div_0 r_0 z_3 y_3))
		(div_0 (Z_2 r_0) x_17 y_3))))
(assert (forall ((x_17 Nat_0) (y_3 Nat_0))
	(=> (lt_0 x_17 y_3)
	    (mod_0 x_17 x_17 y_3))))
(assert (forall ((r_0 Nat_0) (x_17 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (ge_0 x_17 y_3)
			(minus_0 z_3 x_17 y_3)
			(mod_0 r_0 z_3 y_3))
		(mod_0 r_0 x_17 y_3))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_19 Nat_0) (x_20 list_0))
	(head_1 x_19 (cons_0 x_19 x_20))))
(assert (forall ((x_19 Nat_0) (x_20 list_0))
	(tail_1 x_20 (cons_0 x_19 x_20))))
(assert (isnil_0 nil_0))
(assert (forall ((x_22 Nat_0) (x_23 list_0))
	(iscons_0 (cons_0 x_22 x_23))))
(assert (forall ((x_24 Nat_0) (x_25 list_0))
	(diseqlist_0 nil_0 (cons_0 x_24 x_25))))
(assert (forall ((x_26 Nat_0) (x_27 list_0))
	(diseqlist_0 (cons_0 x_26 x_27) nil_0)))
(assert (forall ((x_28 Nat_0) (x_29 list_0) (x_30 Nat_0) (x_31 list_0))
	(=> (diseqNat_0 x_28 x_30)
	    (diseqlist_0 (cons_0 x_28 x_29) (cons_0 x_30 x_31)))))
(assert (forall ((x_28 Nat_0) (x_29 list_0) (x_30 Nat_0) (x_31 list_0))
	(=> (diseqlist_0 x_29 x_31)
	    (diseqlist_0 (cons_0 x_28 x_29) (cons_0 x_30 x_31)))))
(declare-fun x_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_5 list_0) (z_0 Nat_0) (xs_0 list_0) (y_0 list_0))
	(=> (x_0 x_5 xs_0 y_0)
	    (x_0 (cons_0 z_0 x_5) (cons_0 z_0 xs_0) y_0))))
(assert (forall ((x_6 list_0))
	(x_0 x_6 nil_0 x_6)))
(declare-fun rev_0 (list_0 list_0) Bool)
(assert (forall ((x_7 list_0) (x_8 list_0) (y_1 Nat_0) (xs_1 list_0))
	(=>	(and (rev_0 x_8 xs_1)
			(x_0 x_7 x_8 (cons_0 y_1 nil_0)))
		(rev_0 x_7 (cons_0 y_1 xs_1)))))
(assert (rev_0 nil_0 nil_0))
(assert (forall ((x_11 list_0) (x_12 list_0) (x_13 list_0) (x_14 list_0) (x_15 list_0) (x_16 list_0) (x_3 list_0) (y_2 list_0))
	(=>	(and (diseqlist_0 x_13 x_16)
			(rev_0 x_11 x_3)
			(rev_0 x_12 x_11)
			(x_0 x_13 x_12 y_2)
			(x_0 x_14 x_3 y_2)
			(rev_0 x_15 x_14)
			(rev_0 x_16 x_15))
		false)))
(check-sat)
