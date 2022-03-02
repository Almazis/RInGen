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
(assert (forall ((x_38 Nat_0))
	(projS_1 x_38 (S_0 x_38))))
(assert (isZ_2 Z_0))
(assert (forall ((x_40 Nat_0))
	(isS_0 (S_0 x_40))))
(assert (forall ((x_41 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_41))))
(assert (forall ((x_42 Nat_0))
	(diseqNat_0 (S_0 x_42) Z_0)))
(assert (forall ((x_43 Nat_0) (x_44 Nat_0))
	(=> (diseqNat_0 x_43 x_44)
	    (diseqNat_0 (S_0 x_43) (S_0 x_44)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_46 Nat_0) (x_47 list_0))
	(head_1 x_46 (cons_0 x_46 x_47))))
(assert (forall ((x_46 Nat_0) (x_47 list_0))
	(tail_1 x_47 (cons_0 x_46 x_47))))
(assert (isnil_0 nil_0))
(assert (forall ((x_49 Nat_0) (x_50 list_0))
	(iscons_0 (cons_0 x_49 x_50))))
(assert (forall ((x_51 Nat_0) (x_52 list_0))
	(diseqlist_0 nil_0 (cons_0 x_51 x_52))))
(assert (forall ((x_53 Nat_0) (x_54 list_0))
	(diseqlist_0 (cons_0 x_53 x_54) nil_0)))
(assert (forall ((x_55 Nat_0) (x_56 list_0) (x_57 Nat_0) (x_58 list_0))
	(=> (diseqNat_0 x_55 x_57)
	    (diseqlist_0 (cons_0 x_55 x_56) (cons_0 x_57 x_58)))))
(assert (forall ((x_55 Nat_0) (x_56 list_0) (x_57 Nat_0) (x_58 list_0))
	(=> (diseqlist_0 x_56 x_58)
	    (diseqlist_0 (cons_0 x_55 x_56) (cons_0 x_57 x_58)))))
(declare-fun x_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Bool_0) (y_1 Nat_0) (x_2 Nat_0))
	(=> (x_0 x_10 x_2 y_1)
	    (x_0 x_10 (S_0 x_2) (S_0 y_1)))))
(assert (forall ((x_2 Nat_0))
	(x_0 false_0 (S_0 x_2) Z_0)))
(assert (forall ((z_1 Nat_0))
	(x_0 false_0 Z_0 (S_0 z_1))))
(assert (x_0 true_0 Z_0 Z_0))
(declare-fun elem_0 (Bool_0 Nat_0 list_0) Bool)
(assert (forall ((z_2 Nat_0) (xs_0 list_0) (x_3 Nat_0))
	(=> (x_0 true_0 x_3 z_2)
	    (elem_0 true_0 x_3 (cons_0 z_2 xs_0)))))
(assert (forall ((x_17 Bool_0) (x_16 Bool_0) (z_2 Nat_0) (xs_0 list_0) (x_3 Nat_0))
	(=>	(and (diseqBool_0 x_16 true_0)
			(elem_0 x_17 x_3 xs_0)
			(x_0 x_16 x_3 z_2))
		(elem_0 x_17 x_3 (cons_0 z_2 xs_0)))))
(assert (forall ((x_3 Nat_0))
	(elem_0 false_0 x_3 nil_0)))
(declare-fun x_4 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_20 Bool_0) (x_6 Nat_0) (z_3 Nat_0))
	(=> (x_4 x_20 x_6 z_3)
	    (x_4 x_20 (S_0 x_6) (S_0 z_3)))))
(assert (forall ((z_3 Nat_0))
	(x_4 true_0 Z_0 (S_0 z_3))))
(assert (forall ((x_5 Nat_0))
	(x_4 false_0 x_5 Z_0)))
(declare-fun ins_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_4 Nat_0) (xs_1 list_0) (x_7 Nat_0))
	(=> (x_4 true_0 x_7 z_4)
	    (ins_0 (cons_0 x_7 (cons_0 z_4 xs_1)) x_7 (cons_0 z_4 xs_1)))))
(assert (forall ((x_28 list_0) (x_26 Bool_0) (z_4 Nat_0) (xs_1 list_0) (x_7 Nat_0))
	(=>	(and (diseqBool_0 x_26 true_0)
			(ins_0 x_28 x_7 xs_1)
			(x_4 x_26 x_7 z_4))
		(ins_0 (cons_0 z_4 x_28) x_7 (cons_0 z_4 xs_1)))))
(assert (forall ((x_7 Nat_0))
	(ins_0 (cons_0 x_7 nil_0) x_7 nil_0)))
(assert (forall ((x_33 Bool_0) (x_30 list_0) (x_31 Bool_0) (x_32 Bool_0) (x_8 Nat_0) (y_5 Nat_0) (xs_2 list_0))
	(=>	(and (diseqBool_0 x_31 x_32)
			(diseqBool_0 x_33 true_0)
			(x_0 x_33 x_8 y_5)
			(ins_0 x_30 y_5 xs_2)
			(elem_0 x_31 x_8 x_30)
			(elem_0 x_32 x_8 xs_2))
		false)))
(check-sat)
