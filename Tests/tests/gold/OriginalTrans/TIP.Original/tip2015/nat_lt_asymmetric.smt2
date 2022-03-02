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
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_12 Nat_0))
	(p_1 x_12 (succ_0 x_12))))
(assert (iszero_0 zero_0))
(assert (forall ((x_14 Nat_0))
	(issucc_0 (succ_0 x_14))))
(assert (forall ((x_15 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_15))))
(assert (forall ((x_16 Nat_0))
	(diseqNat_0 (succ_0 x_16) zero_0)))
(assert (forall ((x_17 Nat_0) (x_18 Nat_0))
	(=> (diseqNat_0 x_17 x_18)
	    (diseqNat_0 (succ_0 x_17) (succ_0 x_18)))))
(declare-fun lt_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_2 Bool_0) (n_0 Nat_0) (z_0 Nat_0))
	(=> (lt_0 x_2 n_0 z_0)
	    (lt_0 x_2 (succ_0 n_0) (succ_0 z_0)))))
(assert (forall ((z_0 Nat_0))
	(lt_0 true_0 zero_0 (succ_0 z_0))))
(assert (forall ((x_0 Nat_0))
	(lt_0 false_0 x_0 zero_0)))
(assert (forall ((x_1 Nat_0) (y_1 Nat_0))
	(=>	(and (lt_0 true_0 x_1 y_1)
			(lt_0 true_0 y_1 x_1))
		false)))
(check-sat)
