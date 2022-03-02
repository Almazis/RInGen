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
(assert (forall ((x_36 Nat_0))
	(projS_1 x_36 (S_0 x_36))))
(assert (isZ_2 Z_0))
(assert (forall ((x_38 Nat_0))
	(isS_0 (S_0 x_38))))
(assert (forall ((x_39 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_39))))
(assert (forall ((x_40 Nat_0))
	(diseqNat_0 (S_0 x_40) Z_0)))
(assert (forall ((x_41 Nat_0) (x_42 Nat_0))
	(=> (diseqNat_0 x_41 x_42)
	    (diseqNat_0 (S_0 x_41) (S_0 x_42)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_44 Nat_0) (x_45 list_0))
	(head_1 x_44 (cons_0 x_44 x_45))))
(assert (forall ((x_44 Nat_0) (x_45 list_0))
	(tail_1 x_45 (cons_0 x_44 x_45))))
(assert (isnil_0 nil_0))
(assert (forall ((x_47 Nat_0) (x_48 list_0))
	(iscons_0 (cons_0 x_47 x_48))))
(assert (forall ((x_49 Nat_0) (x_50 list_0))
	(diseqlist_0 nil_0 (cons_0 x_49 x_50))))
(assert (forall ((x_51 Nat_0) (x_52 list_0))
	(diseqlist_0 (cons_0 x_51 x_52) nil_0)))
(assert (forall ((x_53 Nat_0) (x_54 list_0) (x_55 Nat_0) (x_56 list_0))
	(=> (diseqNat_0 x_53 x_55)
	    (diseqlist_0 (cons_0 x_53 x_54) (cons_0 x_55 x_56)))))
(assert (forall ((x_53 Nat_0) (x_54 list_0) (x_55 Nat_0) (x_56 list_0))
	(=> (diseqlist_0 x_54 x_56)
	    (diseqlist_0 (cons_0 x_53 x_54) (cons_0 x_55 x_56)))))
(declare-fun x_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_8 Bool_0) (x_2 Nat_0) (z_1 Nat_0))
	(=> (x_0 x_8 z_1 x_2)
	    (x_0 x_8 (S_0 z_1) (S_0 x_2)))))
(assert (forall ((z_1 Nat_0))
	(x_0 false_0 (S_0 z_1) Z_0)))
(assert (forall ((y_0 Nat_0))
	(x_0 true_0 Z_0 y_0)))
(declare-fun insort_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_2 Nat_0) (xs_0 list_0) (x_3 Nat_0))
	(=> (x_0 true_0 x_3 z_2)
	    (insort_0 (cons_0 x_3 (cons_0 z_2 xs_0)) x_3 (cons_0 z_2 xs_0)))))
(assert (forall ((x_16 list_0) (x_14 Bool_0) (z_2 Nat_0) (xs_0 list_0) (x_3 Nat_0))
	(=>	(and (diseqBool_0 x_14 true_0)
			(insort_0 x_16 x_3 xs_0)
			(x_0 x_14 x_3 z_2))
		(insort_0 (cons_0 z_2 x_16) x_3 (cons_0 z_2 xs_0)))))
(assert (forall ((x_3 Nat_0))
	(insort_0 (cons_0 x_3 nil_0) x_3 nil_0)))
(declare-fun sort_0 (list_0 list_0) Bool)
(assert (forall ((x_18 list_0) (x_19 list_0) (y_2 Nat_0) (xs_1 list_0))
	(=>	(and (sort_0 x_19 xs_1)
			(insort_0 x_18 y_2 x_19))
		(sort_0 x_18 (cons_0 y_2 xs_1)))))
(assert (sort_0 nil_0 nil_0))
(declare-fun x_5 (Bool_0 Bool_0 Bool_0) Bool)
(assert (forall ((x_22 Bool_0))
	(x_5 x_22 true_0 x_22)))
(assert (forall ((x_6 Bool_0) (y_3 Bool_0))
	(=> (diseqBool_0 x_6 true_0)
	    (x_5 false_0 x_6 y_3))))
(declare-fun sorted_0 (Bool_0 list_0) Bool)
(assert (forall ((x_24 Bool_0) (x_25 Bool_0) (x_26 Bool_0) (y_5 Nat_0) (ys_0 list_0) (y_4 Nat_0))
	(=>	(and (x_0 x_25 y_4 y_5)
			(sorted_0 x_26 (cons_0 y_5 ys_0))
			(x_5 x_24 x_25 x_26))
		(sorted_0 x_24 (cons_0 y_4 (cons_0 y_5 ys_0))))))
(assert (forall ((y_4 Nat_0))
	(sorted_0 true_0 (cons_0 y_4 nil_0))))
(assert (sorted_0 true_0 nil_0))
(assert (forall ((x_30 list_0) (x_31 Bool_0) (xs_2 list_0))
	(=>	(and (diseqBool_0 x_31 true_0)
			(sort_0 x_30 xs_2)
			(sorted_0 x_31 x_30))
		false)))
(check-sat)
