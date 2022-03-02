(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_3 ) (Z_4 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_50 Nat_1))
	(unS_1 x_50 (Z_4 x_50))))
(assert (isZ_3 Z_3))
(assert (forall ((x_52 Nat_1))
	(isZ_4 (Z_4 x_52))))
(assert (forall ((x_53 Nat_1))
	(diseqNat_1 Z_3 (Z_4 x_53))))
(assert (forall ((x_54 Nat_1))
	(diseqNat_1 (Z_4 x_54) Z_3)))
(assert (forall ((x_55 Nat_1) (x_56 Nat_1))
	(=> (diseqNat_1 x_55 x_56)
	    (diseqNat_1 (Z_4 x_55) (Z_4 x_56)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_5 Nat_1))
	(add_0 y_5 Z_3 y_5)))
(assert (forall ((r_0 Nat_1) (x_26 Nat_1) (y_5 Nat_1))
	(=> (add_0 r_0 x_26 y_5)
	    (add_0 (Z_4 r_0) (Z_4 x_26) y_5))))
(assert (forall ((y_5 Nat_1))
	(minus_0 Z_3 Z_3 y_5)))
(assert (forall ((r_0 Nat_1) (x_26 Nat_1) (y_5 Nat_1))
	(=> (minus_0 r_0 x_26 y_5)
	    (minus_0 (Z_4 r_0) (Z_4 x_26) y_5))))
(assert (forall ((y_5 Nat_1))
	(le_0 Z_3 y_5)))
(assert (forall ((x_26 Nat_1) (y_5 Nat_1))
	(=> (le_0 x_26 y_5)
	    (le_0 (Z_4 x_26) (Z_4 y_5)))))
(assert (forall ((y_5 Nat_1))
	(ge_0 y_5 Z_3)))
(assert (forall ((x_26 Nat_1) (y_5 Nat_1))
	(=> (ge_0 x_26 y_5)
	    (ge_0 (Z_4 x_26) (Z_4 y_5)))))
(assert (forall ((y_5 Nat_1))
	(lt_0 Z_3 (Z_4 y_5))))
(assert (forall ((x_26 Nat_1) (y_5 Nat_1))
	(=> (lt_0 x_26 y_5)
	    (lt_0 (Z_4 x_26) (Z_4 y_5)))))
(assert (forall ((y_5 Nat_1))
	(gt_0 (Z_4 y_5) Z_3)))
(assert (forall ((x_26 Nat_1) (y_5 Nat_1))
	(=> (gt_0 x_26 y_5)
	    (gt_0 (Z_4 x_26) (Z_4 y_5)))))
(assert (forall ((y_5 Nat_1))
	(mult_0 Z_3 Z_3 y_5)))
(assert (forall ((r_0 Nat_1) (x_26 Nat_1) (y_5 Nat_1) (z_5 Nat_1))
	(=>	(and (mult_0 r_0 x_26 y_5)
			(add_0 z_5 r_0 y_5))
		(mult_0 z_5 (Z_4 x_26) y_5))))
(assert (forall ((x_26 Nat_1) (y_5 Nat_1))
	(=> (lt_0 x_26 y_5)
	    (div_0 Z_3 x_26 y_5))))
(assert (forall ((r_0 Nat_1) (x_26 Nat_1) (y_5 Nat_1) (z_5 Nat_1))
	(=>	(and (ge_0 x_26 y_5)
			(minus_0 z_5 x_26 y_5)
			(div_0 r_0 z_5 y_5))
		(div_0 (Z_4 r_0) x_26 y_5))))
(assert (forall ((x_26 Nat_1) (y_5 Nat_1))
	(=> (lt_0 x_26 y_5)
	    (mod_0 x_26 x_26 y_5))))
(assert (forall ((r_0 Nat_1) (x_26 Nat_1) (y_5 Nat_1) (z_5 Nat_1))
	(=>	(and (ge_0 x_26 y_5)
			(minus_0 z_5 x_26 y_5)
			(mod_0 r_0 z_5 y_5))
		(mod_0 r_0 x_26 y_5))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_28 Nat_1) (x_29 list_0))
	(head_1 x_28 (cons_0 x_28 x_29))))
(assert (forall ((x_28 Nat_1) (x_29 list_0))
	(tail_1 x_29 (cons_0 x_28 x_29))))
(assert (isnil_0 nil_0))
(assert (forall ((x_31 Nat_1) (x_32 list_0))
	(iscons_0 (cons_0 x_31 x_32))))
(assert (forall ((x_33 Nat_1) (x_34 list_0))
	(diseqlist_0 nil_0 (cons_0 x_33 x_34))))
(assert (forall ((x_35 Nat_1) (x_36 list_0))
	(diseqlist_0 (cons_0 x_35 x_36) nil_0)))
(assert (forall ((x_37 Nat_1) (x_38 list_0) (x_39 Nat_1) (x_40 list_0))
	(=> (diseqNat_1 x_37 x_39)
	    (diseqlist_0 (cons_0 x_37 x_38) (cons_0 x_39 x_40)))))
(assert (forall ((x_37 Nat_1) (x_38 list_0) (x_39 Nat_1) (x_40 list_0))
	(=> (diseqlist_0 x_38 x_40)
	    (diseqlist_0 (cons_0 x_37 x_38) (cons_0 x_39 x_40)))))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_42 Nat_0))
	(projS_1 x_42 (S_0 x_42))))
(assert (isZ_2 Z_0))
(assert (forall ((x_44 Nat_0))
	(isS_0 (S_0 x_44))))
(assert (forall ((x_45 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_45))))
(assert (forall ((x_46 Nat_0))
	(diseqNat_0 (S_0 x_46) Z_0)))
(assert (forall ((x_47 Nat_0) (x_48 Nat_0))
	(=> (diseqNat_0 x_47 x_48)
	    (diseqNat_0 (S_0 x_47) (S_0 x_48)))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_8 Nat_0) (y_0 Nat_1) (xs_0 list_0))
	(=> (length_0 x_8 xs_0)
	    (length_0 (S_0 x_8) (cons_0 y_0 xs_0)))))
(assert (length_0 Z_0 nil_0))
(declare-fun x_1 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_11 Nat_0) (z_1 Nat_0) (y_1 Nat_0))
	(=> (x_1 x_11 z_1 y_1)
	    (x_1 (S_0 x_11) (S_0 z_1) y_1))))
(assert (forall ((x_12 Nat_0))
	(x_1 x_12 Z_0 x_12)))
(declare-fun x_3 (list_0 list_0 list_0) Bool)
(assert (forall ((x_14 list_0) (z_2 Nat_1) (xs_1 list_0) (y_2 list_0))
	(=> (x_3 x_14 xs_1 y_2)
	    (x_3 (cons_0 z_2 x_14) (cons_0 z_2 xs_1) y_2))))
(assert (forall ((x_15 list_0))
	(x_3 x_15 nil_0 x_15)))
(declare-fun rev_0 (list_0 list_0) Bool)
(assert (forall ((x_16 list_0) (x_17 list_0) (y_3 Nat_1) (xs_2 list_0))
	(=>	(and (rev_0 x_17 xs_2)
			(x_3 x_16 x_17 (cons_0 y_3 nil_0)))
		(rev_0 x_16 (cons_0 y_3 xs_2)))))
(assert (rev_0 nil_0 nil_0))
(assert (forall ((x_20 list_0) (x_21 list_0) (x_22 Nat_0) (x_23 Nat_0) (x_24 Nat_0) (x_25 Nat_0) (x_6 list_0) (y_4 list_0))
	(=>	(and (diseqNat_0 x_22 x_25)
			(x_3 x_20 x_6 y_4)
			(rev_0 x_21 x_20)
			(length_0 x_22 x_21)
			(length_0 x_23 x_6)
			(length_0 x_24 y_4)
			(x_1 x_25 x_23 x_24))
		false)))
(check-sat)
