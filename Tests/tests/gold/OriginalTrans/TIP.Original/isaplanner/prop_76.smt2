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
(assert (forall ((x_29 Nat_0))
	(projS_1 x_29 (S_0 x_29))))
(assert (isZ_2 Z_0))
(assert (forall ((x_31 Nat_0))
	(isS_0 (S_0 x_31))))
(assert (forall ((x_32 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_32))))
(assert (forall ((x_33 Nat_0))
	(diseqNat_0 (S_0 x_33) Z_0)))
(assert (forall ((x_34 Nat_0) (x_35 Nat_0))
	(=> (diseqNat_0 x_34 x_35)
	    (diseqNat_0 (S_0 x_34) (S_0 x_35)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_37 Nat_0) (x_38 list_0))
	(head_1 x_37 (cons_0 x_37 x_38))))
(assert (forall ((x_37 Nat_0) (x_38 list_0))
	(tail_1 x_38 (cons_0 x_37 x_38))))
(assert (isnil_0 nil_0))
(assert (forall ((x_40 Nat_0) (x_41 list_0))
	(iscons_0 (cons_0 x_40 x_41))))
(assert (forall ((x_42 Nat_0) (x_43 list_0))
	(diseqlist_0 nil_0 (cons_0 x_42 x_43))))
(assert (forall ((x_44 Nat_0) (x_45 list_0))
	(diseqlist_0 (cons_0 x_44 x_45) nil_0)))
(assert (forall ((x_46 Nat_0) (x_47 list_0) (x_48 Nat_0) (x_49 list_0))
	(=> (diseqNat_0 x_46 x_48)
	    (diseqlist_0 (cons_0 x_46 x_47) (cons_0 x_48 x_49)))))
(assert (forall ((x_46 Nat_0) (x_47 list_0) (x_48 Nat_0) (x_49 list_0))
	(=> (diseqlist_0 x_47 x_49)
	    (diseqlist_0 (cons_0 x_46 x_47) (cons_0 x_48 x_49)))))
(declare-fun x_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_6 Bool_0) (y_1 Nat_0) (x_2 Nat_0))
	(=> (x_0 x_6 x_2 y_1)
	    (x_0 x_6 (S_0 x_2) (S_0 y_1)))))
(assert (forall ((x_2 Nat_0))
	(x_0 false_0 (S_0 x_2) Z_0)))
(assert (forall ((z_1 Nat_0))
	(x_0 false_0 Z_0 (S_0 z_1))))
(assert (x_0 true_0 Z_0 Z_0))
(declare-fun count_0 (Nat_0 Nat_0 list_0) Bool)
(assert (forall ((x_13 Nat_0) (z_2 Nat_0) (ys_0 list_0) (x_3 Nat_0))
	(=>	(and (count_0 x_13 x_3 ys_0)
			(x_0 true_0 x_3 z_2))
		(count_0 (S_0 x_13) x_3 (cons_0 z_2 ys_0)))))
(assert (forall ((x_15 Nat_0) (x_14 Bool_0) (z_2 Nat_0) (ys_0 list_0) (x_3 Nat_0))
	(=>	(and (diseqBool_0 x_14 true_0)
			(count_0 x_15 x_3 ys_0)
			(x_0 x_14 x_3 z_2))
		(count_0 x_15 x_3 (cons_0 z_2 ys_0)))))
(assert (forall ((x_3 Nat_0))
	(count_0 Z_0 x_3 nil_0)))
(declare-fun x_4 (list_0 list_0 list_0) Bool)
(assert (forall ((x_19 list_0) (z_3 Nat_0) (xs_0 list_0) (y_3 list_0))
	(=> (x_4 x_19 xs_0 y_3)
	    (x_4 (cons_0 z_3 x_19) (cons_0 z_3 xs_0) y_3))))
(assert (forall ((x_20 list_0))
	(x_4 x_20 nil_0 x_20)))
(assert (forall ((x_24 Bool_0) (x_21 list_0) (x_22 Nat_0) (x_23 Nat_0) (n_0 Nat_0) (m_0 Nat_0) (xs_1 list_0))
	(=>	(and (diseqNat_0 x_22 x_23)
			(diseqBool_0 x_24 true_0)
			(x_0 x_24 n_0 m_0)
			(x_4 x_21 xs_1 (cons_0 m_0 nil_0))
			(count_0 x_22 n_0 x_21)
			(count_0 x_23 n_0 xs_1))
		false)))
(check-sat)
