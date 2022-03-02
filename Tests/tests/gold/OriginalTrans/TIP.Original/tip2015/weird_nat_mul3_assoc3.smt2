(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_116 Nat_0))
	(p_1 x_116 (succ_0 x_116))))
(assert (iszero_0 zero_0))
(assert (forall ((x_118 Nat_0))
	(issucc_0 (succ_0 x_118))))
(assert (forall ((x_119 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_119))))
(assert (forall ((x_120 Nat_0))
	(diseqNat_0 (succ_0 x_120) zero_0)))
(assert (forall ((x_121 Nat_0) (x_122 Nat_0))
	(=> (diseqNat_0 x_121 x_122)
	    (diseqNat_0 (succ_0 x_121) (succ_0 x_122)))))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_18 Nat_0) (z_0 Nat_0) (y_0 Nat_0))
	(=> (plus_0 x_18 z_0 y_0)
	    (plus_0 (succ_0 x_18) (succ_0 z_0) y_0))))
(assert (forall ((x_19 Nat_0))
	(plus_0 x_19 zero_0 x_19)))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_20 Nat_0) (x_21 Nat_0) (x_3 Nat_0) (y_1 Nat_0) (z_1 Nat_0))
	(=>	(and (add_0 x_21 x_3 y_1 z_1)
			(plus_0 x_20 (succ_0 zero_0) x_21))
		(add_0 x_20 (succ_0 x_3) y_1 z_1))))
(assert (forall ((x_23 Nat_0) (x_24 Nat_0) (x_2 Nat_0) (z_1 Nat_0))
	(=>	(and (add_0 x_24 zero_0 x_2 z_1)
			(plus_0 x_23 (succ_0 zero_0) x_24))
		(add_0 x_23 zero_0 (succ_0 x_2) z_1))))
(assert (forall ((x_26 Nat_0))
	(add_0 x_26 zero_0 zero_0 x_26)))
(declare-fun mul_0 (Nat_0 Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_27 Nat_0) (x_28 Nat_0) (x_29 Nat_0) (x_30 Nat_0) (x_31 Nat_0) (x_32 Nat_0) (x_33 Nat_0) (fail_0 Nat_0))
	(=>	(and (mul_0 x_27 zero_0 zero_0 zero_0)
			(mul_0 x_28 (succ_0 zero_0) zero_0 zero_0)
			(mul_0 x_29 zero_0 (succ_0 zero_0) zero_0)
			(mul_0 x_30 zero_0 zero_0 (succ_0 zero_0))
			(add_0 x_31 x_28 x_29 x_30)
			(add_0 x_32 zero_0 zero_0 zero_0)
			(add_0 x_33 x_27 x_31 x_32)
			(plus_0 fail_0 (succ_0 zero_0) x_33))
		(mul_0 (succ_0 zero_0) (succ_0 zero_0) (succ_0 zero_0) (succ_0 zero_0)))))
(assert (forall ((x_36 Nat_0) (x_37 Nat_0) (x_38 Nat_0) (x_39 Nat_0) (x_40 Nat_0) (x_41 Nat_0) (x_42 Nat_0) (fail_0 Nat_0) (x_7 Nat_0) (x_6 Nat_0) (x_5 Nat_0))
	(=>	(and (diseqNat_0 x_5 zero_0)
			(mul_0 x_36 x_5 x_6 x_7)
			(mul_0 x_37 (succ_0 zero_0) x_6 x_7)
			(mul_0 x_38 x_5 (succ_0 zero_0) x_7)
			(mul_0 x_39 x_5 x_6 (succ_0 zero_0))
			(add_0 x_40 x_37 x_38 x_39)
			(add_0 x_41 x_5 x_6 x_7)
			(add_0 x_42 x_36 x_40 x_41)
			(plus_0 fail_0 (succ_0 zero_0) x_42))
		(mul_0 fail_0 (succ_0 x_5) (succ_0 x_6) (succ_0 x_7)))))
(assert (forall ((x_45 Nat_0) (x_46 Nat_0) (x_47 Nat_0) (x_48 Nat_0) (x_49 Nat_0) (x_50 Nat_0) (x_51 Nat_0) (fail_0 Nat_0) (x_7 Nat_0) (x_6 Nat_0))
	(=>	(and (diseqNat_0 x_6 zero_0)
			(mul_0 x_45 zero_0 x_6 x_7)
			(mul_0 x_46 (succ_0 zero_0) x_6 x_7)
			(mul_0 x_47 zero_0 (succ_0 zero_0) x_7)
			(mul_0 x_48 zero_0 x_6 (succ_0 zero_0))
			(add_0 x_49 x_46 x_47 x_48)
			(add_0 x_50 zero_0 x_6 x_7)
			(add_0 x_51 x_45 x_49 x_50)
			(plus_0 fail_0 (succ_0 zero_0) x_51))
		(mul_0 fail_0 (succ_0 zero_0) (succ_0 x_6) (succ_0 x_7)))))
(assert (forall ((x_54 Nat_0) (x_55 Nat_0) (x_56 Nat_0) (x_57 Nat_0) (x_58 Nat_0) (x_59 Nat_0) (x_60 Nat_0) (fail_0 Nat_0) (x_7 Nat_0) (x_6 Nat_0) (x_5 Nat_0))
	(=>	(and (diseqNat_0 x_5 zero_0)
			(mul_0 x_54 x_5 x_6 x_7)
			(mul_0 x_55 (succ_0 zero_0) x_6 x_7)
			(mul_0 x_56 x_5 (succ_0 zero_0) x_7)
			(mul_0 x_57 x_5 x_6 (succ_0 zero_0))
			(add_0 x_58 x_55 x_56 x_57)
			(add_0 x_59 x_5 x_6 x_7)
			(add_0 x_60 x_54 x_58 x_59)
			(plus_0 fail_0 (succ_0 zero_0) x_60))
		(mul_0 fail_0 (succ_0 x_5) (succ_0 x_6) (succ_0 x_7)))))
(assert (forall ((x_63 Nat_0) (x_64 Nat_0) (x_65 Nat_0) (x_66 Nat_0) (x_67 Nat_0) (x_68 Nat_0) (x_69 Nat_0) (fail_0 Nat_0) (x_7 Nat_0))
	(=>	(and (diseqNat_0 x_7 zero_0)
			(mul_0 x_63 zero_0 zero_0 x_7)
			(mul_0 x_64 (succ_0 zero_0) zero_0 x_7)
			(mul_0 x_65 zero_0 (succ_0 zero_0) x_7)
			(mul_0 x_66 zero_0 zero_0 (succ_0 zero_0))
			(add_0 x_67 x_64 x_65 x_66)
			(add_0 x_68 zero_0 zero_0 x_7)
			(add_0 x_69 x_63 x_67 x_68)
			(plus_0 fail_0 (succ_0 zero_0) x_69))
		(mul_0 fail_0 (succ_0 zero_0) (succ_0 zero_0) (succ_0 x_7)))))
(assert (forall ((x_72 Nat_0) (x_73 Nat_0) (x_74 Nat_0) (x_75 Nat_0) (x_76 Nat_0) (x_77 Nat_0) (x_78 Nat_0) (fail_0 Nat_0) (x_7 Nat_0) (x_6 Nat_0) (x_5 Nat_0))
	(=>	(and (diseqNat_0 x_5 zero_0)
			(mul_0 x_72 x_5 x_6 x_7)
			(mul_0 x_73 (succ_0 zero_0) x_6 x_7)
			(mul_0 x_74 x_5 (succ_0 zero_0) x_7)
			(mul_0 x_75 x_5 x_6 (succ_0 zero_0))
			(add_0 x_76 x_73 x_74 x_75)
			(add_0 x_77 x_5 x_6 x_7)
			(add_0 x_78 x_72 x_76 x_77)
			(plus_0 fail_0 (succ_0 zero_0) x_78))
		(mul_0 fail_0 (succ_0 x_5) (succ_0 x_6) (succ_0 x_7)))))
(assert (forall ((x_81 Nat_0) (x_82 Nat_0) (x_83 Nat_0) (x_84 Nat_0) (x_85 Nat_0) (x_86 Nat_0) (x_87 Nat_0) (fail_0 Nat_0) (x_7 Nat_0) (x_6 Nat_0))
	(=>	(and (diseqNat_0 x_6 zero_0)
			(mul_0 x_81 zero_0 x_6 x_7)
			(mul_0 x_82 (succ_0 zero_0) x_6 x_7)
			(mul_0 x_83 zero_0 (succ_0 zero_0) x_7)
			(mul_0 x_84 zero_0 x_6 (succ_0 zero_0))
			(add_0 x_85 x_82 x_83 x_84)
			(add_0 x_86 zero_0 x_6 x_7)
			(add_0 x_87 x_81 x_85 x_86)
			(plus_0 fail_0 (succ_0 zero_0) x_87))
		(mul_0 fail_0 (succ_0 zero_0) (succ_0 x_6) (succ_0 x_7)))))
(assert (forall ((x_90 Nat_0) (x_91 Nat_0) (x_92 Nat_0) (x_93 Nat_0) (x_94 Nat_0) (x_95 Nat_0) (x_96 Nat_0) (fail_0 Nat_0) (x_7 Nat_0) (x_6 Nat_0) (x_5 Nat_0))
	(=>	(and (diseqNat_0 x_5 zero_0)
			(mul_0 x_90 x_5 x_6 x_7)
			(mul_0 x_91 (succ_0 zero_0) x_6 x_7)
			(mul_0 x_92 x_5 (succ_0 zero_0) x_7)
			(mul_0 x_93 x_5 x_6 (succ_0 zero_0))
			(add_0 x_94 x_91 x_92 x_93)
			(add_0 x_95 x_5 x_6 x_7)
			(add_0 x_96 x_90 x_94 x_95)
			(plus_0 fail_0 (succ_0 zero_0) x_96))
		(mul_0 fail_0 (succ_0 x_5) (succ_0 x_6) (succ_0 x_7)))))
(assert (forall ((x_6 Nat_0) (x_5 Nat_0))
	(mul_0 zero_0 (succ_0 x_5) (succ_0 x_6) zero_0)))
(assert (forall ((x_5 Nat_0) (z_2 Nat_0))
	(mul_0 zero_0 (succ_0 x_5) zero_0 z_2)))
(assert (forall ((y_2 Nat_0) (z_2 Nat_0))
	(mul_0 zero_0 zero_0 y_2 z_2)))
(assert (forall ((x_102 Nat_0) (x_103 Nat_0) (x_104 Nat_0) (x_105 Nat_0) (x_8 Nat_0) (x_9 Nat_0) (x_10 Nat_0) (x_11 Nat_0) (x_12 Nat_0))
	(=>	(and (diseqNat_0 x_103 x_105)
			(mul_0 x_102 x_9 x_10 x_11)
			(mul_0 x_103 x_8 x_102 x_12)
			(mul_0 x_104 x_10 x_11 x_12)
			(mul_0 x_105 x_8 x_9 x_104))
		false)))
(assert (forall ((x_106 Nat_0) (x_107 Nat_0) (x_108 Nat_0) (x_109 Nat_0) (x_13 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=>	(and (diseqNat_0 x_107 x_109)
			(plus_0 x_106 y_3 z_3)
			(plus_0 x_107 x_13 x_106)
			(plus_0 x_108 x_13 y_3)
			(plus_0 x_109 x_108 z_3))
		false)))
(assert (forall ((x_110 Nat_0) (x_111 Nat_0) (x_14 Nat_0) (y_4 Nat_0))
	(=>	(and (diseqNat_0 x_110 x_111)
			(plus_0 x_110 x_14 y_4)
			(plus_0 x_111 y_4 x_14))
		false)))
(assert (forall ((x_112 Nat_0) (x_15 Nat_0))
	(=>	(and (diseqNat_0 x_112 x_15)
			(plus_0 x_112 x_15 zero_0))
		false)))
(assert (forall ((x_113 Nat_0) (x_16 Nat_0))
	(=>	(and (diseqNat_0 x_113 x_16)
			(plus_0 x_113 zero_0 x_16))
		false)))
(check-sat)
