(set-logic HORN)
(declare-datatypes ((Bool_0 0)) (((false_0 ) (true_0 ))))
(declare-fun diseqBool_0 (Bool_0 Bool_0) Bool)
(declare-fun isfalse_1 (Bool_0) Bool)
(declare-fun istrue_1 (Bool_0) Bool)
(assert (isfalse_1 false_0))
(assert (istrue_1 true_0))
(assert (diseqBool_0 false_0 true_0))
(assert (diseqBool_0 true_0 false_0))
(declare-fun and_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun or_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun hence_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun not_0 (Bool_0 Bool_0) Bool)
(assert (and_0 false_0 false_0 false_0))
(assert (and_0 false_0 true_0 false_0))
(assert (and_0 false_0 false_0 true_0))
(assert (and_0 true_0 true_0 true_0))
(assert (or_0 false_0 false_0 false_0))
(assert (or_0 true_0 true_0 false_0))
(assert (or_0 true_0 false_0 true_0))
(assert (or_0 true_0 true_0 true_0))
(assert (hence_0 true_0 false_0 false_0))
(assert (hence_0 false_0 true_0 false_0))
(assert (hence_0 true_0 false_0 true_0))
(assert (hence_0 true_0 true_0 true_0))
(assert (not_0 true_0 false_0))
(assert (not_0 false_0 true_0))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_34 Nat_0))
	(projS_1 x_34 (S_0 x_34))))
(assert (isZ_2 Z_0))
(assert (forall ((x_36 Nat_0))
	(isS_0 (S_0 x_36))))
(assert (forall ((x_37 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_37))))
(assert (forall ((x_38 Nat_0))
	(diseqNat_0 (S_0 x_38) Z_0)))
(assert (forall ((x_39 Nat_0) (x_40 Nat_0))
	(=> (diseqNat_0 x_39 x_40)
	    (diseqNat_0 (S_0 x_39) (S_0 x_40)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_42 Nat_0) (x_43 list_0))
	(head_1 x_42 (cons_0 x_42 x_43))))
(assert (forall ((x_42 Nat_0) (x_43 list_0))
	(tail_1 x_43 (cons_0 x_42 x_43))))
(assert (isnil_0 nil_0))
(assert (forall ((x_45 Nat_0) (x_46 list_0))
	(iscons_0 (cons_0 x_45 x_46))))
(assert (forall ((x_47 Nat_0) (x_48 list_0))
	(diseqlist_0 nil_0 (cons_0 x_47 x_48))))
(assert (forall ((x_49 Nat_0) (x_50 list_0))
	(diseqlist_0 (cons_0 x_49 x_50) nil_0)))
(assert (forall ((x_51 Nat_0) (x_52 list_0) (x_53 Nat_0) (x_54 list_0))
	(=> (diseqNat_0 x_51 x_53)
	    (diseqlist_0 (cons_0 x_51 x_52) (cons_0 x_53 x_54)))))
(assert (forall ((x_51 Nat_0) (x_52 list_0) (x_53 Nat_0) (x_54 list_0))
	(=> (diseqlist_0 x_52 x_54)
	    (diseqlist_0 (cons_0 x_51 x_52) (cons_0 x_53 x_54)))))
(declare-fun barbar_0 (Bool_0 Bool_0 Bool_0) Bool)
(assert (forall ((y_0 Bool_0))
	(barbar_0 true_0 true_0 y_0)))
(assert (forall ((x_8 Bool_0) (x_0 Bool_0))
	(=> (diseqBool_0 x_0 true_0)
	    (barbar_0 x_8 x_0 x_8))))
(declare-fun x_1 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Bool_0) (y_2 Nat_0) (x_3 Nat_0))
	(=> (x_1 x_10 x_3 y_2)
	    (x_1 x_10 (S_0 x_3) (S_0 y_2)))))
(assert (forall ((x_3 Nat_0))
	(x_1 false_0 (S_0 x_3) Z_0)))
(assert (forall ((z_1 Nat_0))
	(x_1 false_0 Z_0 (S_0 z_1))))
(assert (x_1 true_0 Z_0 Z_0))
(declare-fun elem_0 (Bool_0 Nat_0 list_0) Bool)
(assert (forall ((x_14 Bool_0) (x_15 Bool_0) (x_16 Bool_0) (z_2 Nat_0) (xs_0 list_0) (x_4 Nat_0))
	(=>	(and (x_1 x_15 x_4 z_2)
			(elem_0 x_16 x_4 xs_0)
			(barbar_0 x_14 x_15 x_16))
		(elem_0 x_14 x_4 (cons_0 z_2 xs_0)))))
(assert (forall ((x_4 Nat_0))
	(elem_0 false_0 x_4 nil_0)))
(declare-fun intersect_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_21 list_0) (z_3 Nat_0) (xs_1 list_0) (y_4 list_0))
	(=>	(and (intersect_0 x_21 xs_1 y_4)
			(elem_0 true_0 z_3 y_4))
		(intersect_0 (cons_0 z_3 x_21) (cons_0 z_3 xs_1) y_4))))
(assert (forall ((x_23 list_0) (x_22 Bool_0) (z_3 Nat_0) (xs_1 list_0) (y_4 list_0))
	(=>	(and (diseqBool_0 x_22 true_0)
			(intersect_0 x_23 xs_1 y_4)
			(elem_0 x_22 z_3 y_4))
		(intersect_0 x_23 (cons_0 z_3 xs_1) y_4))))
(assert (forall ((y_4 list_0))
	(intersect_0 nil_0 nil_0 y_4)))
(assert (forall ((x_26 list_0) (x_27 Bool_0) (x_6 Nat_0) (y_5 list_0) (z_4 list_0))
	(=>	(and (diseqBool_0 x_27 true_0)
			(elem_0 true_0 x_6 y_5)
			(elem_0 true_0 x_6 z_4)
			(intersect_0 x_26 y_5 z_4)
			(elem_0 x_27 x_6 x_26))
		false)))
(check-sat)
