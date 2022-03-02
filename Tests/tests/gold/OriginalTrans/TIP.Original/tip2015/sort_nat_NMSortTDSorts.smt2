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
(assert (forall ((x_88 Nat_0))
	(p_1 x_88 (succ_0 x_88))))
(assert (iszero_0 zero_0))
(assert (forall ((x_90 Nat_0))
	(issucc_0 (succ_0 x_90))))
(assert (forall ((x_91 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_91))))
(assert (forall ((x_92 Nat_0))
	(diseqNat_0 (succ_0 x_92) zero_0)))
(assert (forall ((x_93 Nat_0) (x_94 Nat_0))
	(=> (diseqNat_0 x_93 x_94)
	    (diseqNat_0 (succ_0 x_93) (succ_0 x_94)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_96 Nat_0) (x_97 list_0))
	(head_1 x_96 (cons_0 x_96 x_97))))
(assert (forall ((x_96 Nat_0) (x_97 list_0))
	(tail_1 x_97 (cons_0 x_96 x_97))))
(assert (isnil_0 nil_0))
(assert (forall ((x_100 list_0) (x_99 Nat_0))
	(iscons_0 (cons_0 x_99 x_100))))
(assert (forall ((x_101 Nat_0) (x_102 list_0))
	(diseqlist_0 nil_0 (cons_0 x_101 x_102))))
(assert (forall ((x_103 Nat_0) (x_104 list_0))
	(diseqlist_0 (cons_0 x_103 x_104) nil_0)))
(assert (forall ((x_105 Nat_0) (x_106 list_0) (x_107 Nat_0) (x_108 list_0))
	(=> (diseqNat_0 x_105 x_107)
	    (diseqlist_0 (cons_0 x_105 x_106) (cons_0 x_107 x_108)))))
(assert (forall ((x_105 Nat_0) (x_106 list_0) (x_107 Nat_0) (x_108 list_0))
	(=> (diseqlist_0 x_106 x_108)
	    (diseqlist_0 (cons_0 x_105 x_106) (cons_0 x_107 x_108)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_21 list_0) (z_1 Nat_0) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_21 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_21) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_25 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_25 z_2 y_1)
	    (plus_0 (succ_0 x_25) (succ_0 z_2) y_1))))
(assert (forall ((x_26 Nat_0))
	(plus_0 x_26 zero_0 x_26)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_27 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=> (minus_0 x_27 z_3 y_3)
	    (minus_0 x_27 (succ_0 z_3) (succ_0 y_3)))))
(assert (forall ((z_3 Nat_0))
	(minus_0 zero_0 (succ_0 z_3) zero_0)))
(assert (forall ((y_2 Nat_0))
	(minus_0 zero_0 zero_0 y_2)))
(declare-fun nmsorttdhalf_0 (Nat_0 Nat_0) Bool)
(assert (nmsorttdhalf_0 zero_0 (succ_0 zero_0)))
(assert (forall ((x_32 Nat_0) (x_33 Nat_0) (x_34 Nat_0) (y_4 Nat_0))
	(=>	(and (diseqNat_0 (succ_0 y_4) (succ_0 zero_0))
			(minus_0 x_33 (succ_0 y_4) (succ_0 (succ_0 zero_0)))
			(nmsorttdhalf_0 x_34 x_33)
			(plus_0 x_32 (succ_0 zero_0) x_34))
		(nmsorttdhalf_0 x_32 (succ_0 y_4)))))
(assert (nmsorttdhalf_0 zero_0 (succ_0 zero_0)))
(assert (=> (diseqNat_0 zero_0 (succ_0 zero_0))
	    (nmsorttdhalf_0 zero_0 zero_0)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_38 Bool_0) (x_5 Nat_0) (z_4 Nat_0))
	(=> (leq_0 x_38 z_4 x_5)
	    (leq_0 x_38 (succ_0 z_4) (succ_0 x_5)))))
(assert (forall ((z_4 Nat_0))
	(leq_0 false_0 (succ_0 z_4) zero_0)))
(assert (forall ((y_5 Nat_0))
	(leq_0 true_0 zero_0 y_5)))
(declare-fun lmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_44 list_0) (x_8 Nat_0) (x_9 list_0) (z_5 Nat_0) (x_7 list_0))
	(=>	(and (lmerge_0 x_44 x_7 (cons_0 x_8 x_9))
			(leq_0 true_0 z_5 x_8))
		(lmerge_0 (cons_0 z_5 x_44) (cons_0 z_5 x_7) (cons_0 x_8 x_9)))))
(assert (forall ((x_47 list_0) (x_45 Bool_0) (x_8 Nat_0) (x_9 list_0) (z_5 Nat_0) (x_7 list_0))
	(=>	(and (diseqBool_0 x_45 true_0)
			(lmerge_0 x_47 (cons_0 z_5 x_7) x_9)
			(leq_0 x_45 z_5 x_8))
		(lmerge_0 (cons_0 x_8 x_47) (cons_0 z_5 x_7) (cons_0 x_8 x_9)))))
(assert (forall ((z_5 Nat_0) (x_7 list_0))
	(lmerge_0 (cons_0 z_5 x_7) (cons_0 z_5 x_7) nil_0)))
(assert (forall ((x_49 list_0))
	(lmerge_0 x_49 nil_0 x_49)))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_50 Bool_0) (x_51 Bool_0) (x_52 Bool_0) (y_8 Nat_0) (xs_1 list_0) (y_7 Nat_0))
	(=>	(and (leq_0 x_51 y_7 y_8)
			(ordered_0 x_52 (cons_0 y_8 xs_1))
			(and_0 x_50 x_51 x_52))
		(ordered_0 x_50 (cons_0 y_7 (cons_0 y_8 xs_1))))))
(assert (forall ((y_7 Nat_0))
	(ordered_0 true_0 (cons_0 y_7 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_55 Nat_0) (x_56 Nat_0) (y_9 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_56 l_0)
			(plus_0 x_55 (succ_0 zero_0) x_56))
		(length_0 x_55 (cons_0 y_9 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_59 list_0) (z_8 Nat_0) (xs_2 list_0) (z_7 Nat_0))
	(=> (drop_0 x_59 z_7 xs_2)
	    (drop_0 x_59 (succ_0 z_7) (cons_0 z_8 xs_2)))))
(assert (forall ((z_7 Nat_0))
	(drop_0 nil_0 (succ_0 z_7) nil_0)))
(assert (forall ((x_62 list_0))
	(drop_0 x_62 zero_0 x_62)))
(declare-fun nmsorttd_0 (list_0 list_0) Bool)
(assert (forall ((x_65 list_0) (x_66 list_0) (x_67 list_0) (x_68 list_0) (x_69 list_0) (x_63 Nat_0) (k_0 Nat_0) (x_14 Nat_0) (x_15 list_0) (y_11 Nat_0))
	(=>	(and (take_0 x_66 k_0 (cons_0 y_11 (cons_0 x_14 x_15)))
			(nmsorttd_0 x_67 x_66)
			(drop_0 x_68 k_0 (cons_0 y_11 (cons_0 x_14 x_15)))
			(nmsorttd_0 x_69 x_68)
			(lmerge_0 x_65 x_67 x_69)
			(length_0 x_63 (cons_0 y_11 (cons_0 x_14 x_15)))
			(nmsorttdhalf_0 k_0 x_63))
		(nmsorttd_0 x_65 (cons_0 y_11 (cons_0 x_14 x_15))))))
(assert (forall ((y_11 Nat_0))
	(nmsorttd_0 (cons_0 y_11 nil_0) (cons_0 y_11 nil_0))))
(assert (nmsorttd_0 nil_0 nil_0))
(assert (forall ((x_73 Nat_0) (x_74 Nat_0) (x_75 Nat_0) (x_76 Nat_0) (x_16 Nat_0) (y_12 Nat_0) (z_10 Nat_0))
	(=>	(and (diseqNat_0 x_74 x_76)
			(plus_0 x_73 y_12 z_10)
			(plus_0 x_74 x_16 x_73)
			(plus_0 x_75 x_16 y_12)
			(plus_0 x_76 x_75 z_10))
		false)))
(assert (forall ((x_77 Nat_0) (x_78 Nat_0) (x_17 Nat_0) (y_13 Nat_0))
	(=>	(and (diseqNat_0 x_77 x_78)
			(plus_0 x_77 x_17 y_13)
			(plus_0 x_78 y_13 x_17))
		false)))
(assert (forall ((x_79 Nat_0) (x_18 Nat_0))
	(=>	(and (diseqNat_0 x_79 x_18)
			(plus_0 x_79 x_18 zero_0))
		false)))
(assert (forall ((x_80 Nat_0) (x_19 Nat_0))
	(=>	(and (diseqNat_0 x_80 x_19)
			(plus_0 x_80 zero_0 x_19))
		false)))
(assert (forall ((x_81 list_0) (x_82 Bool_0) (xs_3 list_0))
	(=>	(and (diseqBool_0 x_82 true_0)
			(nmsorttd_0 x_81 xs_3)
			(ordered_0 x_82 x_81))
		false)))
(check-sat)
