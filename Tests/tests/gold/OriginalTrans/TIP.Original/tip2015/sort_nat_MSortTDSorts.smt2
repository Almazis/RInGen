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
(assert (forall ((x_92 Nat_0))
	(p_1 x_92 (succ_0 x_92))))
(assert (iszero_0 zero_0))
(assert (forall ((x_94 Nat_0))
	(issucc_0 (succ_0 x_94))))
(assert (forall ((x_95 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_95))))
(assert (forall ((x_96 Nat_0))
	(diseqNat_0 (succ_0 x_96) zero_0)))
(assert (forall ((x_97 Nat_0) (x_98 Nat_0))
	(=> (diseqNat_0 x_97 x_98)
	    (diseqNat_0 (succ_0 x_97) (succ_0 x_98)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_100 Nat_0) (x_101 list_0))
	(head_1 x_100 (cons_0 x_100 x_101))))
(assert (forall ((x_100 Nat_0) (x_101 list_0))
	(tail_1 x_101 (cons_0 x_100 x_101))))
(assert (isnil_0 nil_0))
(assert (forall ((x_103 Nat_0) (x_104 list_0))
	(iscons_0 (cons_0 x_103 x_104))))
(assert (forall ((x_105 Nat_0) (x_106 list_0))
	(diseqlist_0 nil_0 (cons_0 x_105 x_106))))
(assert (forall ((x_107 Nat_0) (x_108 list_0))
	(diseqlist_0 (cons_0 x_107 x_108) nil_0)))
(assert (forall ((x_109 Nat_0) (x_110 list_0) (x_111 Nat_0) (x_112 list_0))
	(=> (diseqNat_0 x_109 x_111)
	    (diseqlist_0 (cons_0 x_109 x_110) (cons_0 x_111 x_112)))))
(assert (forall ((x_109 Nat_0) (x_110 list_0) (x_111 Nat_0) (x_112 list_0))
	(=> (diseqlist_0 x_110 x_112)
	    (diseqlist_0 (cons_0 x_109 x_110) (cons_0 x_111 x_112)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_22 list_0) (z_1 Nat_0) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_22 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_22) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_26 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_26 z_2 y_1)
	    (plus_0 (succ_0 x_26) (succ_0 z_2) y_1))))
(assert (forall ((x_27 Nat_0))
	(plus_0 x_27 zero_0 x_27)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_28 Nat_0) (y_3 Nat_0) (z_3 Nat_0))
	(=> (minus_0 x_28 z_3 y_3)
	    (minus_0 x_28 (succ_0 z_3) (succ_0 y_3)))))
(assert (forall ((z_3 Nat_0))
	(minus_0 zero_0 (succ_0 z_3) zero_0)))
(assert (forall ((y_2 Nat_0))
	(minus_0 zero_0 zero_0 y_2)))
(declare-fun lt_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_32 Bool_0) (n_0 Nat_0) (z_4 Nat_0))
	(=> (lt_0 x_32 n_0 z_4)
	    (lt_0 x_32 (succ_0 n_0) (succ_0 z_4)))))
(assert (forall ((z_4 Nat_0))
	(lt_0 true_0 zero_0 (succ_0 z_4))))
(assert (forall ((x_3 Nat_0))
	(lt_0 false_0 x_3 zero_0)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_36 Bool_0) (x_5 Nat_0) (z_5 Nat_0))
	(=> (leq_0 x_36 z_5 x_5)
	    (leq_0 x_36 (succ_0 z_5) (succ_0 x_5)))))
(assert (forall ((z_5 Nat_0))
	(leq_0 false_0 (succ_0 z_5) zero_0)))
(assert (forall ((y_5 Nat_0))
	(leq_0 true_0 zero_0 y_5)))
(declare-fun lmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_42 list_0) (x_8 Nat_0) (x_9 list_0) (z_6 Nat_0) (x_7 list_0))
	(=>	(and (lmerge_0 x_42 x_7 (cons_0 x_8 x_9))
			(leq_0 true_0 z_6 x_8))
		(lmerge_0 (cons_0 z_6 x_42) (cons_0 z_6 x_7) (cons_0 x_8 x_9)))))
(assert (forall ((x_45 list_0) (x_43 Bool_0) (x_8 Nat_0) (x_9 list_0) (z_6 Nat_0) (x_7 list_0))
	(=>	(and (diseqBool_0 x_43 true_0)
			(lmerge_0 x_45 (cons_0 z_6 x_7) x_9)
			(leq_0 x_43 z_6 x_8))
		(lmerge_0 (cons_0 x_8 x_45) (cons_0 z_6 x_7) (cons_0 x_8 x_9)))))
(assert (forall ((z_6 Nat_0) (x_7 list_0))
	(lmerge_0 (cons_0 z_6 x_7) (cons_0 z_6 x_7) nil_0)))
(assert (forall ((x_47 list_0))
	(lmerge_0 x_47 nil_0 x_47)))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_48 Bool_0) (x_49 Bool_0) (x_50 Bool_0) (y_8 Nat_0) (xs_1 list_0) (y_7 Nat_0))
	(=>	(and (leq_0 x_49 y_7 y_8)
			(ordered_0 x_50 (cons_0 y_8 xs_1))
			(and_0 x_48 x_49 x_50))
		(ordered_0 x_48 (cons_0 y_7 (cons_0 y_8 xs_1))))))
(assert (forall ((y_7 Nat_0))
	(ordered_0 true_0 (cons_0 y_7 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_53 Nat_0) (x_54 Nat_0) (y_9 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_54 l_0)
			(plus_0 x_53 (succ_0 zero_0) x_54))
		(length_0 x_53 (cons_0 y_9 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun idiv_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_12 Nat_0) (y_10 Nat_0))
	(=> (lt_0 true_0 x_12 y_10)
	    (idiv_0 zero_0 x_12 y_10))))
(assert (forall ((x_61 Nat_0) (x_62 Nat_0) (x_59 Bool_0) (x_12 Nat_0) (y_10 Nat_0))
	(=>	(and (diseqBool_0 x_59 true_0)
			(minus_0 x_61 x_12 y_10)
			(idiv_0 x_62 x_61 y_10)
			(lt_0 x_59 x_12 y_10))
		(idiv_0 (succ_0 x_62) x_12 y_10))))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_63 list_0) (z_9 Nat_0) (xs_2 list_0) (z_8 Nat_0))
	(=> (drop_0 x_63 z_8 xs_2)
	    (drop_0 x_63 (succ_0 z_8) (cons_0 z_9 xs_2)))))
(assert (forall ((z_8 Nat_0))
	(drop_0 nil_0 (succ_0 z_8) nil_0)))
(assert (forall ((x_66 list_0))
	(drop_0 x_66 zero_0 x_66)))
(declare-fun msorttd_0 (list_0 list_0) Bool)
(assert (forall ((x_69 list_0) (x_70 list_0) (x_71 list_0) (x_72 list_0) (x_73 list_0) (x_67 Nat_0) (k_0 Nat_0) (x_15 Nat_0) (x_16 list_0) (y_12 Nat_0))
	(=>	(and (take_0 x_70 k_0 (cons_0 y_12 (cons_0 x_15 x_16)))
			(msorttd_0 x_71 x_70)
			(drop_0 x_72 k_0 (cons_0 y_12 (cons_0 x_15 x_16)))
			(msorttd_0 x_73 x_72)
			(lmerge_0 x_69 x_71 x_73)
			(length_0 x_67 (cons_0 y_12 (cons_0 x_15 x_16)))
			(idiv_0 k_0 x_67 (succ_0 (succ_0 zero_0))))
		(msorttd_0 x_69 (cons_0 y_12 (cons_0 x_15 x_16))))))
(assert (forall ((y_12 Nat_0))
	(msorttd_0 (cons_0 y_12 nil_0) (cons_0 y_12 nil_0))))
(assert (msorttd_0 nil_0 nil_0))
(assert (forall ((x_77 Nat_0) (x_78 Nat_0) (x_79 Nat_0) (x_80 Nat_0) (x_17 Nat_0) (y_13 Nat_0) (z_11 Nat_0))
	(=>	(and (diseqNat_0 x_78 x_80)
			(plus_0 x_77 y_13 z_11)
			(plus_0 x_78 x_17 x_77)
			(plus_0 x_79 x_17 y_13)
			(plus_0 x_80 x_79 z_11))
		false)))
(assert (forall ((x_81 Nat_0) (x_82 Nat_0) (x_18 Nat_0) (y_14 Nat_0))
	(=>	(and (diseqNat_0 x_81 x_82)
			(plus_0 x_81 x_18 y_14)
			(plus_0 x_82 y_14 x_18))
		false)))
(assert (forall ((x_83 Nat_0) (x_19 Nat_0))
	(=>	(and (diseqNat_0 x_83 x_19)
			(plus_0 x_83 x_19 zero_0))
		false)))
(assert (forall ((x_84 Nat_0) (x_20 Nat_0))
	(=>	(and (diseqNat_0 x_84 x_20)
			(plus_0 x_84 zero_0 x_20))
		false)))
(assert (forall ((x_85 list_0) (x_86 Bool_0) (xs_3 list_0))
	(=>	(and (diseqBool_0 x_86 true_0)
			(msorttd_0 x_85 xs_3)
			(ordered_0 x_86 x_85))
		false)))
(check-sat)
