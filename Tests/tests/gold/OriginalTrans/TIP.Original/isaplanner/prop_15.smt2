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
(assert (forall ((x_26 Nat_0))
	(projS_1 x_26 (S_0 x_26))))
(assert (isZ_2 Z_0))
(assert (forall ((x_28 Nat_0))
	(isS_0 (S_0 x_28))))
(assert (forall ((x_29 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_29))))
(assert (forall ((x_30 Nat_0))
	(diseqNat_0 (S_0 x_30) Z_0)))
(assert (forall ((x_31 Nat_0) (x_32 Nat_0))
	(=> (diseqNat_0 x_31 x_32)
	    (diseqNat_0 (S_0 x_31) (S_0 x_32)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_34 Nat_0) (x_35 list_0))
	(head_1 x_34 (cons_0 x_34 x_35))))
(assert (forall ((x_34 Nat_0) (x_35 list_0))
	(tail_1 x_35 (cons_0 x_34 x_35))))
(assert (isnil_0 nil_0))
(assert (forall ((x_37 Nat_0) (x_38 list_0))
	(iscons_0 (cons_0 x_37 x_38))))
(assert (forall ((x_39 Nat_0) (x_40 list_0))
	(diseqlist_0 nil_0 (cons_0 x_39 x_40))))
(assert (forall ((x_41 Nat_0) (x_42 list_0))
	(diseqlist_0 (cons_0 x_41 x_42) nil_0)))
(assert (forall ((x_43 Nat_0) (x_44 list_0) (x_45 Nat_0) (x_46 list_0))
	(=> (diseqNat_0 x_43 x_45)
	    (diseqlist_0 (cons_0 x_43 x_44) (cons_0 x_45 x_46)))))
(assert (forall ((x_43 Nat_0) (x_44 list_0) (x_45 Nat_0) (x_46 list_0))
	(=> (diseqlist_0 x_44 x_46)
	    (diseqlist_0 (cons_0 x_43 x_44) (cons_0 x_45 x_46)))))
(declare-fun len_0 (Nat_0 list_0) Bool)
(assert (forall ((x_7 Nat_0) (y_0 Nat_0) (xs_0 list_0))
	(=> (len_0 x_7 xs_0)
	    (len_0 (S_0 x_7) (cons_0 y_0 xs_0)))))
(assert (len_0 Z_0 nil_0))
(declare-fun x_1 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Bool_0) (x_3 Nat_0) (z_1 Nat_0))
	(=> (x_1 x_10 x_3 z_1)
	    (x_1 x_10 (S_0 x_3) (S_0 z_1)))))
(assert (forall ((z_1 Nat_0))
	(x_1 true_0 Z_0 (S_0 z_1))))
(assert (forall ((x_2 Nat_0))
	(x_1 false_0 x_2 Z_0)))
(declare-fun ins_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_2 Nat_0) (xs_1 list_0) (x_4 Nat_0))
	(=> (x_1 true_0 x_4 z_2)
	    (ins_0 (cons_0 x_4 (cons_0 z_2 xs_1)) x_4 (cons_0 z_2 xs_1)))))
(assert (forall ((x_17 list_0) (x_15 Bool_0) (z_2 Nat_0) (xs_1 list_0) (x_4 Nat_0))
	(=>	(and (diseqBool_0 x_15 true_0)
			(ins_0 x_17 x_4 xs_1)
			(x_1 x_15 x_4 z_2))
		(ins_0 (cons_0 z_2 x_17) x_4 (cons_0 z_2 xs_1)))))
(assert (forall ((x_4 Nat_0))
	(ins_0 (cons_0 x_4 nil_0) x_4 nil_0)))
(assert (forall ((x_19 list_0) (x_20 Nat_0) (x_21 Nat_0) (x_5 Nat_0) (xs_2 list_0))
	(=>	(and (diseqNat_0 x_20 (S_0 x_21))
			(ins_0 x_19 x_5 xs_2)
			(len_0 x_20 x_19)
			(len_0 x_21 xs_2))
		false)))
(check-sat)
