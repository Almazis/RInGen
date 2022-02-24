(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (prev_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun prev_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_4 Nat_0))
	(prev_1 x_4 (S_0 x_4))))
(assert (isZ_2 Z_0))
(assert (forall ((x_6 Nat_0))
	(isS_0 (S_0 x_6))))
(assert (forall ((x_7 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_7))))
(assert (forall ((x_8 Nat_0))
	(diseqNat_0 (S_0 x_8) Z_0)))
(assert (forall ((x_10 Nat_0) (x_9 Nat_0))
	(=> (diseqNat_0 x_9 x_10)
	    (diseqNat_0 (S_0 x_9) (S_0 x_10)))))
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(assert (forall ((y_0 Nat_0))
	(lt_0 Z_0 (S_0 y_0))))
(assert (forall ((x_0 Nat_0) (y_1 Nat_0))
	(=> (lt_0 x_0 y_1)
	    (lt_0 (S_0 x_0) (S_0 y_1)))))
(assert (forall ((x_1 Nat_0) (y_2 Nat_0))
	(=>	(and (lt_0 x_1 y_2)
			(lt_0 y_2 x_1))
		false)))
(check-sat)
