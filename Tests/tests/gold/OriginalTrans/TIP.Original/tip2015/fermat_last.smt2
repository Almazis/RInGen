(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_77 Nat_0))
	(p_1 x_77 (succ_0 x_77))))
(assert (iszero_0 zero_0))
(assert (forall ((x_79 Nat_0))
	(issucc_0 (succ_0 x_79))))
(assert (forall ((x_80 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_80))))
(assert (forall ((x_81 Nat_0))
	(diseqNat_0 (succ_0 x_81) zero_0)))
(assert (forall ((x_82 Nat_0) (x_83 Nat_0))
	(=> (diseqNat_0 x_82 x_83)
	    (diseqNat_0 (succ_0 x_82) (succ_0 x_83)))))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_19 Nat_0) (z_0 Nat_0) (y_0 Nat_0))
	(=> (plus_0 x_19 z_0 y_0)
	    (plus_0 (succ_0 x_19) (succ_0 z_0) y_0))))
(assert (forall ((x_20 Nat_0))
	(plus_0 x_20 zero_0 x_20)))
(declare-fun times_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_21 Nat_0) (x_22 Nat_0) (z_1 Nat_0) (y_1 Nat_0))
	(=>	(and (times_0 x_22 z_1 y_1)
			(plus_0 x_21 y_1 x_22))
		(times_0 x_21 (succ_0 z_1) y_1))))
(assert (forall ((y_1 Nat_0))
	(times_0 zero_0 zero_0 y_1)))
(declare-fun formulapow_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_25 Nat_0) (x_26 Nat_0) (z_2 Nat_0) (x_2 Nat_0))
	(=>	(and (formulapow_0 x_26 x_2 z_2)
			(times_0 x_25 x_2 x_26))
		(formulapow_0 x_25 x_2 (succ_0 z_2)))))
(assert (forall ((x_2 Nat_0))
	(formulapow_0 (succ_0 zero_0) x_2 zero_0)))
(declare-fun formulapow_1 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_29 Nat_0) (x_30 Nat_0) (z_3 Nat_0) (x_3 Nat_0))
	(=>	(and (formulapow_1 x_30 x_3 z_3)
			(times_0 x_29 x_3 x_30))
		(formulapow_1 x_29 x_3 (succ_0 z_3)))))
(assert (forall ((x_3 Nat_0))
	(formulapow_1 (succ_0 zero_0) x_3 zero_0)))
(declare-fun formulapow_2 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_33 Nat_0) (x_34 Nat_0) (z_4 Nat_0) (x_4 Nat_0))
	(=>	(and (formulapow_2 x_34 x_4 z_4)
			(times_0 x_33 x_4 x_34))
		(formulapow_2 x_33 x_4 (succ_0 z_4)))))
(assert (forall ((x_4 Nat_0))
	(formulapow_2 (succ_0 zero_0) x_4 zero_0)))
(assert (forall ((x_37 Nat_0) (x_38 Nat_0) (x_39 Nat_0) (x_40 Nat_0) (x_41 Nat_0) (x_42 Nat_0) (x_43 Nat_0) (x_44 Nat_0) (x_45 Nat_0) (n_0 Nat_0) (x_5 Nat_0) (y_5 Nat_0) (z_5 Nat_0))
	(=>	(and (plus_0 x_37 (succ_0 zero_0) x_5)
			(plus_0 x_38 (succ_0 (succ_0 (succ_0 zero_0))) n_0)
			(formulapow_2 x_39 x_37 x_38)
			(plus_0 x_40 (succ_0 zero_0) y_5)
			(plus_0 x_41 (succ_0 (succ_0 (succ_0 zero_0))) n_0)
			(formulapow_1 x_42 x_40 x_41)
			(plus_0 x_43 x_39 x_42)
			(plus_0 x_44 (succ_0 zero_0) z_5)
			(plus_0 x_45 (succ_0 (succ_0 (succ_0 zero_0))) n_0)
			(formulapow_0 x_43 x_44 x_45))
		false)))
(assert (forall ((x_47 Nat_0) (x_48 Nat_0) (x_49 Nat_0) (x_50 Nat_0) (x_6 Nat_0) (y_6 Nat_0) (z_6 Nat_0))
	(=>	(and (diseqNat_0 x_48 x_50)
			(times_0 x_47 y_6 z_6)
			(times_0 x_48 x_6 x_47)
			(times_0 x_49 x_6 y_6)
			(times_0 x_50 x_49 z_6))
		false)))
(assert (forall ((x_51 Nat_0) (x_52 Nat_0) (x_53 Nat_0) (x_54 Nat_0) (x_7 Nat_0) (y_7 Nat_0) (z_7 Nat_0))
	(=>	(and (diseqNat_0 x_52 x_54)
			(plus_0 x_51 y_7 z_7)
			(plus_0 x_52 x_7 x_51)
			(plus_0 x_53 x_7 y_7)
			(plus_0 x_54 x_53 z_7))
		false)))
(assert (forall ((x_55 Nat_0) (x_56 Nat_0) (x_8 Nat_0) (y_8 Nat_0))
	(=>	(and (diseqNat_0 x_55 x_56)
			(times_0 x_55 x_8 y_8)
			(times_0 x_56 y_8 x_8))
		false)))
(assert (forall ((x_57 Nat_0) (x_58 Nat_0) (x_9 Nat_0) (y_9 Nat_0))
	(=>	(and (diseqNat_0 x_57 x_58)
			(plus_0 x_57 x_9 y_9)
			(plus_0 x_58 y_9 x_9))
		false)))
(assert (forall ((x_59 Nat_0) (x_60 Nat_0) (x_61 Nat_0) (x_62 Nat_0) (x_63 Nat_0) (x_10 Nat_0) (y_10 Nat_0) (z_8 Nat_0))
	(=>	(and (diseqNat_0 x_60 x_63)
			(plus_0 x_59 y_10 z_8)
			(times_0 x_60 x_10 x_59)
			(times_0 x_61 x_10 y_10)
			(times_0 x_62 x_10 z_8)
			(plus_0 x_63 x_61 x_62))
		false)))
(assert (forall ((x_64 Nat_0) (x_65 Nat_0) (x_66 Nat_0) (x_67 Nat_0) (x_68 Nat_0) (x_11 Nat_0) (y_11 Nat_0) (z_9 Nat_0))
	(=>	(and (diseqNat_0 x_65 x_68)
			(plus_0 x_64 x_11 y_11)
			(times_0 x_65 x_64 z_9)
			(times_0 x_66 x_11 z_9)
			(times_0 x_67 y_11 z_9)
			(plus_0 x_68 x_66 x_67))
		false)))
(assert (forall ((x_69 Nat_0) (x_12 Nat_0))
	(=>	(and (diseqNat_0 x_69 x_12)
			(times_0 x_69 x_12 (succ_0 zero_0)))
		false)))
(assert (forall ((x_70 Nat_0) (x_13 Nat_0))
	(=>	(and (diseqNat_0 x_70 x_13)
			(times_0 x_70 (succ_0 zero_0) x_13))
		false)))
(assert (forall ((x_71 Nat_0) (x_14 Nat_0))
	(=>	(and (diseqNat_0 x_71 x_14)
			(plus_0 x_71 x_14 zero_0))
		false)))
(assert (forall ((x_72 Nat_0) (x_15 Nat_0))
	(=>	(and (diseqNat_0 x_72 x_15)
			(plus_0 x_72 zero_0 x_15))
		false)))
(assert (forall ((x_73 Nat_0) (x_16 Nat_0))
	(=>	(and (diseqNat_0 x_73 zero_0)
			(times_0 x_73 x_16 zero_0))
		false)))
(assert (forall ((x_74 Nat_0) (x_17 Nat_0))
	(=>	(and (diseqNat_0 x_74 zero_0)
			(times_0 x_74 zero_0 x_17))
		false)))
(check-sat)
