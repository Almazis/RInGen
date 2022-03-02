(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_15 Nat_0))
	(p_1 x_15 (succ_0 x_15))))
(assert (iszero_0 zero_0))
(assert (forall ((x_17 Nat_0))
	(issucc_0 (succ_0 x_17))))
(assert (forall ((x_18 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_18))))
(assert (forall ((x_19 Nat_0))
	(diseqNat_0 (succ_0 x_19) zero_0)))
(assert (forall ((x_20 Nat_0) (x_21 Nat_0))
	(=> (diseqNat_0 x_20 x_21)
	    (diseqNat_0 (succ_0 x_20) (succ_0 x_21)))))
(declare-fun op_0 (Nat_0 Nat_0 Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_4 Nat_0) (x_3 Nat_0) (x_0 Nat_0) (y_0 Nat_0) (x_1 Nat_0))
	(=> (op_0 x_4 x_0 y_0 x_3 (succ_0 x_1))
	    (op_0 x_4 x_0 y_0 (succ_0 x_3) x_1))))
(assert (forall ((x_6 Nat_0) (x_2 Nat_0) (y_0 Nat_0) (x_1 Nat_0))
	(=> (op_0 x_6 x_2 y_0 y_0 x_1)
	    (op_0 x_6 (succ_0 x_2) y_0 zero_0 x_1))))
(assert (forall ((y_0 Nat_0) (x_1 Nat_0))
	(op_0 x_1 zero_0 y_0 zero_0 x_1)))
(assert (forall ((x_9 Nat_0) (x_10 Nat_0) (x_11 Nat_0) (x_12 Nat_0) (a_0 Nat_0) (b_0 Nat_0) (c_0 Nat_0) (d_0 Nat_0) (e_0 Nat_0))
	(=>	(and (diseqNat_0 x_10 x_12)
			(op_0 x_9 a_0 b_0 zero_0 zero_0)
			(op_0 x_10 x_9 c_0 d_0 e_0)
			(op_0 x_11 b_0 c_0 zero_0 zero_0)
			(op_0 x_12 a_0 x_11 d_0 e_0))
		false)))
(check-sat)
