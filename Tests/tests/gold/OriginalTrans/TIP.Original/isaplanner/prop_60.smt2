(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_21 Nat_0))
	(projS_1 x_21 (S_0 x_21))))
(assert (isZ_2 Z_0))
(assert (forall ((x_23 Nat_0))
	(isS_0 (S_0 x_23))))
(assert (forall ((x_24 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_24))))
(assert (forall ((x_25 Nat_0))
	(diseqNat_0 (S_0 x_25) Z_0)))
(assert (forall ((x_26 Nat_0) (x_27 Nat_0))
	(=> (diseqNat_0 x_26 x_27)
	    (diseqNat_0 (S_0 x_26) (S_0 x_27)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_29 Nat_0) (x_30 list_0))
	(head_1 x_29 (cons_0 x_29 x_30))))
(assert (forall ((x_29 Nat_0) (x_30 list_0))
	(tail_1 x_30 (cons_0 x_29 x_30))))
(assert (isnil_0 nil_0))
(assert (forall ((x_32 Nat_0) (x_33 list_0))
	(iscons_0 (cons_0 x_32 x_33))))
(assert (forall ((x_34 Nat_0) (x_35 list_0))
	(diseqlist_0 nil_0 (cons_0 x_34 x_35))))
(assert (forall ((x_36 Nat_0) (x_37 list_0))
	(diseqlist_0 (cons_0 x_36 x_37) nil_0)))
(assert (forall ((x_38 Nat_0) (x_39 list_0) (x_40 Nat_0) (x_41 list_0))
	(=> (diseqNat_0 x_38 x_40)
	    (diseqlist_0 (cons_0 x_38 x_39) (cons_0 x_40 x_41)))))
(assert (forall ((x_38 Nat_0) (x_39 list_0) (x_40 Nat_0) (x_41 list_0))
	(=> (diseqlist_0 x_39 x_41)
	    (diseqlist_0 (cons_0 x_38 x_39) (cons_0 x_40 x_41)))))
(declare-fun last_0 (Nat_0 list_0) Bool)
(assert (forall ((x_6 Nat_0) (x_1 Nat_0) (x_2 list_0) (y_0 Nat_0))
	(=> (last_0 x_6 (cons_0 x_1 x_2))
	    (last_0 x_6 (cons_0 y_0 (cons_0 x_1 x_2))))))
(assert (forall ((x_8 Nat_0))
	(last_0 x_8 (cons_0 x_8 nil_0))))
(assert (last_0 Z_0 nil_0))
(declare-fun x_3 (list_0 list_0 list_0) Bool)
(assert (forall ((x_11 list_0) (z_2 Nat_0) (xs_0 list_0) (y_1 list_0))
	(=> (x_3 x_11 xs_0 y_1)
	    (x_3 (cons_0 z_2 x_11) (cons_0 z_2 xs_0) y_1))))
(assert (forall ((x_12 list_0))
	(x_3 x_12 nil_0 x_12)))
(assert (forall ((x_13 list_0) (x_14 Nat_0) (x_15 Nat_0) (x_5 Nat_0) (y_2 list_0) (xs_1 list_0))
	(=>	(and (diseqNat_0 x_14 x_15)
			true
			(x_3 x_13 xs_1 (cons_0 x_5 y_2))
			(last_0 x_14 x_13)
			(last_0 x_15 (cons_0 x_5 y_2)))
		false)))
(assert (forall ((x_16 list_0) (x_17 Nat_0) (x_18 Nat_0) (xs_1 list_0))
	(=>	(and (diseqNat_0 x_17 x_18)
			false
			(x_3 x_16 xs_1 nil_0)
			(last_0 x_17 x_16)
			(last_0 x_18 nil_0))
		false)))
(check-sat)
