(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_31 Nat_0))
	(p_1 x_31 (succ_0 x_31))))
(assert (iszero_0 zero_0))
(assert (forall ((x_33 Nat_0))
	(issucc_0 (succ_0 x_33))))
(assert (forall ((x_34 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_34))))
(assert (forall ((x_35 Nat_0))
	(diseqNat_0 (succ_0 x_35) zero_0)))
(assert (forall ((x_36 Nat_0) (x_37 Nat_0))
	(=> (diseqNat_0 x_36 x_37)
	    (diseqNat_0 (succ_0 x_36) (succ_0 x_37)))))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_10 Nat_0) (z_0 Nat_0) (y_0 Nat_0))
	(=> (plus_0 x_10 z_0 y_0)
	    (plus_0 (succ_0 x_10) (succ_0 z_0) y_0))))
(assert (forall ((x_11 Nat_0))
	(plus_0 x_11 zero_0 x_11)))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_12 Nat_0) (x_13 Nat_0) (x_3 Nat_0) (y_1 Nat_0) (z_1 Nat_0))
	(=>	(and (add_0 x_13 x_3 y_1 z_1)
			(plus_0 x_12 (succ_0 zero_0) x_13))
		(add_0 x_12 (succ_0 x_3) y_1 z_1))))
(assert (forall ((x_15 Nat_0) (x_16 Nat_0) (x_2 Nat_0) (z_1 Nat_0))
	(=>	(and (add_0 x_16 zero_0 x_2 z_1)
			(plus_0 x_15 (succ_0 zero_0) x_16))
		(add_0 x_15 zero_0 (succ_0 x_2) z_1))))
(assert (forall ((x_18 Nat_0))
	(add_0 x_18 zero_0 zero_0 x_18)))
(assert (forall ((x_19 Nat_0) (x_20 Nat_0) (x_4 Nat_0) (y_2 Nat_0) (z_2 Nat_0))
	(=>	(and (diseqNat_0 x_19 x_20)
			(add_0 x_19 x_4 y_2 z_2)
			(add_0 x_20 z_2 y_2 x_4))
		false)))
(assert (forall ((x_21 Nat_0) (x_22 Nat_0) (x_23 Nat_0) (x_24 Nat_0) (x_5 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (diseqNat_0 x_22 x_24)
			(plus_0 x_21 y_3 z_3)
			(plus_0 x_22 x_5 x_21)
			(plus_0 x_23 x_5 y_3)
			(plus_0 x_24 x_23 z_3))
		false)))
(assert (forall ((x_25 Nat_0) (x_26 Nat_0) (x_6 Nat_0) (y_4 Nat_0))
	(=>	(and (diseqNat_0 x_25 x_26)
			(plus_0 x_25 x_6 y_4)
			(plus_0 x_26 y_4 x_6))
		false)))
(assert (forall ((x_27 Nat_0) (x_7 Nat_0))
	(=>	(and (diseqNat_0 x_27 x_7)
			(plus_0 x_27 x_7 zero_0))
		false)))
(assert (forall ((x_28 Nat_0) (x_8 Nat_0))
	(=>	(and (diseqNat_0 x_28 x_8)
			(plus_0 x_28 zero_0 x_8))
		false)))
(check-sat)
