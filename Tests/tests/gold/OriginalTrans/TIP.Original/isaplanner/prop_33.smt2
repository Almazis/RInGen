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
(assert (forall ((x_27 Nat_0))
	(projS_1 x_27 (S_0 x_27))))
(assert (isZ_2 Z_0))
(assert (forall ((x_29 Nat_0))
	(isS_0 (S_0 x_29))))
(assert (forall ((x_30 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_30))))
(assert (forall ((x_31 Nat_0))
	(diseqNat_0 (S_0 x_31) Z_0)))
(assert (forall ((x_32 Nat_0) (x_33 Nat_0))
	(=> (diseqNat_0 x_32 x_33)
	    (diseqNat_0 (S_0 x_32) (S_0 x_33)))))
(declare-fun min_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_8 Nat_0) (y_1 Nat_0) (z_1 Nat_0))
	(=> (min_0 x_8 z_1 y_1)
	    (min_0 (S_0 x_8) (S_0 z_1) (S_0 y_1)))))
(assert (forall ((z_1 Nat_0))
	(min_0 Z_0 (S_0 z_1) Z_0)))
(assert (forall ((y_0 Nat_0))
	(min_0 Z_0 Z_0 y_0)))
(declare-fun x_1 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_11 Bool_0) (y_3 Nat_0) (x_3 Nat_0))
	(=> (x_1 x_11 x_3 y_3)
	    (x_1 x_11 (S_0 x_3) (S_0 y_3)))))
(assert (forall ((x_3 Nat_0))
	(x_1 false_0 (S_0 x_3) Z_0)))
(assert (forall ((z_2 Nat_0))
	(x_1 false_0 Z_0 (S_0 z_2))))
(assert (x_1 true_0 Z_0 Z_0))
(declare-fun x_4 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_16 Bool_0) (x_6 Nat_0) (z_3 Nat_0))
	(=> (x_4 x_16 z_3 x_6)
	    (x_4 x_16 (S_0 z_3) (S_0 x_6)))))
(assert (forall ((z_3 Nat_0))
	(x_4 false_0 (S_0 z_3) Z_0)))
(assert (forall ((y_4 Nat_0))
	(x_4 true_0 Z_0 y_4)))
(assert (forall ((x_20 Nat_0) (x_21 Bool_0) (x_22 Bool_0) (a_0 Nat_0) (b_0 Nat_0))
	(=>	(and (diseqBool_0 x_21 x_22)
			(min_0 x_20 a_0 b_0)
			(x_1 x_21 x_20 a_0)
			(x_4 x_22 a_0 b_0))
		false)))
(check-sat)
