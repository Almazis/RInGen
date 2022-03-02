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
(assert (forall ((x_30 Nat_0))
	(projS_1 x_30 (S_0 x_30))))
(assert (isZ_2 Z_0))
(assert (forall ((x_32 Nat_0))
	(isS_0 (S_0 x_32))))
(assert (forall ((x_33 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_33))))
(assert (forall ((x_34 Nat_0))
	(diseqNat_0 (S_0 x_34) Z_0)))
(assert (forall ((x_35 Nat_0) (x_36 Nat_0))
	(=> (diseqNat_0 x_35 x_36)
	    (diseqNat_0 (S_0 x_35) (S_0 x_36)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_38 Nat_0) (x_39 list_0))
	(head_1 x_38 (cons_0 x_38 x_39))))
(assert (forall ((x_38 Nat_0) (x_39 list_0))
	(tail_1 x_39 (cons_0 x_38 x_39))))
(assert (isnil_0 nil_0))
(assert (forall ((x_41 Nat_0) (x_42 list_0))
	(iscons_0 (cons_0 x_41 x_42))))
(assert (forall ((x_43 Nat_0) (x_44 list_0))
	(diseqlist_0 nil_0 (cons_0 x_43 x_44))))
(assert (forall ((x_45 Nat_0) (x_46 list_0))
	(diseqlist_0 (cons_0 x_45 x_46) nil_0)))
(assert (forall ((x_47 Nat_0) (x_48 list_0) (x_49 Nat_0) (x_50 list_0))
	(=> (diseqNat_0 x_47 x_49)
	    (diseqlist_0 (cons_0 x_47 x_48) (cons_0 x_49 x_50)))))
(assert (forall ((x_47 Nat_0) (x_48 list_0) (x_49 Nat_0) (x_50 list_0))
	(=> (diseqlist_0 x_48 x_50)
	    (diseqlist_0 (cons_0 x_47 x_48) (cons_0 x_49 x_50)))))
(declare-fun x_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_7 Bool_0) (y_1 Nat_0) (x_2 Nat_0))
	(=> (x_0 x_7 x_2 y_1)
	    (x_0 x_7 (S_0 x_2) (S_0 y_1)))))
(assert (forall ((x_2 Nat_0))
	(x_0 false_0 (S_0 x_2) Z_0)))
(assert (forall ((z_1 Nat_0))
	(x_0 false_0 Z_0 (S_0 z_1))))
(assert (x_0 true_0 Z_0 Z_0))
(declare-fun count_0 (Nat_0 Nat_0 list_0) Bool)
(assert (forall ((x_14 Nat_0) (z_2 Nat_0) (ys_0 list_0) (x_3 Nat_0))
	(=>	(and (count_0 x_14 x_3 ys_0)
			(x_0 true_0 x_3 z_2))
		(count_0 (S_0 x_14) x_3 (cons_0 z_2 ys_0)))))
(assert (forall ((x_16 Nat_0) (x_15 Bool_0) (z_2 Nat_0) (ys_0 list_0) (x_3 Nat_0))
	(=>	(and (diseqBool_0 x_15 true_0)
			(count_0 x_16 x_3 ys_0)
			(x_0 x_15 x_3 z_2))
		(count_0 x_16 x_3 (cons_0 z_2 ys_0)))))
(assert (forall ((x_3 Nat_0))
	(count_0 Z_0 x_3 nil_0)))
(declare-fun x_4 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_20 Nat_0) (z_3 Nat_0) (y_3 Nat_0))
	(=> (x_4 x_20 z_3 y_3)
	    (x_4 (S_0 x_20) (S_0 z_3) y_3))))
(assert (forall ((x_21 Nat_0))
	(x_4 x_21 Z_0 x_21)))
(assert (forall ((x_22 Nat_0) (x_23 Nat_0) (x_24 Nat_0) (x_25 Nat_0) (n_0 Nat_0) (x_6 Nat_0) (xs_0 list_0))
	(=>	(and (diseqNat_0 x_24 x_25)
			(count_0 x_22 n_0 (cons_0 x_6 nil_0))
			(count_0 x_23 n_0 xs_0)
			(x_4 x_24 x_22 x_23)
			(count_0 x_25 n_0 (cons_0 x_6 xs_0)))
		false)))
(check-sat)
