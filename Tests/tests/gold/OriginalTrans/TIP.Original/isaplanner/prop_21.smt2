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
(assert (forall ((x_18 Nat_0))
	(projS_1 x_18 (S_0 x_18))))
(assert (isZ_2 Z_0))
(assert (forall ((x_20 Nat_0))
	(isS_0 (S_0 x_20))))
(assert (forall ((x_21 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_21))))
(assert (forall ((x_22 Nat_0))
	(diseqNat_0 (S_0 x_22) Z_0)))
(assert (forall ((x_23 Nat_0) (x_24 Nat_0))
	(=> (diseqNat_0 x_23 x_24)
	    (diseqNat_0 (S_0 x_23) (S_0 x_24)))))
(declare-fun x_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_5 Bool_0) (x_2 Nat_0) (z_1 Nat_0))
	(=> (x_0 x_5 z_1 x_2)
	    (x_0 x_5 (S_0 z_1) (S_0 x_2)))))
(assert (forall ((z_1 Nat_0))
	(x_0 false_0 (S_0 z_1) Z_0)))
(assert (forall ((y_0 Nat_0))
	(x_0 true_0 Z_0 y_0)))
(declare-fun x_3 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (x_3 x_10 z_2 y_1)
	    (x_3 (S_0 x_10) (S_0 z_2) y_1))))
(assert (forall ((x_11 Nat_0))
	(x_3 x_11 Z_0 x_11)))
(assert (forall ((x_12 Nat_0) (x_13 Bool_0) (n_0 Nat_0) (m_0 Nat_0))
	(=>	(and (diseqBool_0 x_13 true_0)
			(x_3 x_12 n_0 m_0)
			(x_0 x_13 n_0 x_12))
		false)))
(check-sat)
