(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_25 Nat_0))
	(p_1 x_25 (succ_0 x_25))))
(assert (iszero_0 zero_0))
(assert (forall ((x_27 Nat_0))
	(issucc_0 (succ_0 x_27))))
(assert (forall ((x_28 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_28))))
(assert (forall ((x_29 Nat_0))
	(diseqNat_0 (succ_0 x_29) zero_0)))
(assert (forall ((x_30 Nat_0) (x_31 Nat_0))
	(=> (diseqNat_0 x_30 x_31)
	    (diseqNat_0 (succ_0 x_30) (succ_0 x_31)))))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_8 Nat_0) (z_0 Nat_0) (y_0 Nat_0))
	(=> (plus_0 x_8 z_0 y_0)
	    (plus_0 (succ_0 x_8) (succ_0 z_0) y_0))))
(assert (forall ((x_9 Nat_0))
	(plus_0 x_9 zero_0 x_9)))
(declare-fun accplus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Nat_0) (z_1 Nat_0) (y_1 Nat_0))
	(=> (accplus_0 x_10 z_1 (succ_0 y_1))
	    (accplus_0 x_10 (succ_0 z_1) y_1))))
(assert (forall ((x_12 Nat_0))
	(accplus_0 x_12 zero_0 x_12)))
(assert (forall ((x_13 Nat_0) (x_14 Nat_0) (x_2 Nat_0) (y_2 Nat_0))
	(=>	(and (diseqNat_0 x_13 x_14)
			(plus_0 x_13 x_2 y_2)
			(accplus_0 x_14 x_2 y_2))
		false)))
(assert (forall ((x_15 Nat_0) (x_16 Nat_0) (x_17 Nat_0) (x_18 Nat_0) (x_3 Nat_0) (y_3 Nat_0) (z_2 Nat_0))
	(=>	(and (diseqNat_0 x_16 x_18)
			(plus_0 x_15 y_3 z_2)
			(plus_0 x_16 x_3 x_15)
			(plus_0 x_17 x_3 y_3)
			(plus_0 x_18 x_17 z_2))
		false)))
(assert (forall ((x_19 Nat_0) (x_20 Nat_0) (x_4 Nat_0) (y_4 Nat_0))
	(=>	(and (diseqNat_0 x_19 x_20)
			(plus_0 x_19 x_4 y_4)
			(plus_0 x_20 y_4 x_4))
		false)))
(assert (forall ((x_21 Nat_0) (x_5 Nat_0))
	(=>	(and (diseqNat_0 x_21 x_5)
			(plus_0 x_21 x_5 zero_0))
		false)))
(assert (forall ((x_22 Nat_0) (x_6 Nat_0))
	(=>	(and (diseqNat_0 x_22 x_6)
			(plus_0 x_22 zero_0 x_6))
		false)))
(check-sat)
