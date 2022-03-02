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
(assert (forall ((x_146 Nat_0))
	(p_1 x_146 (succ_0 x_146))))
(assert (iszero_0 zero_0))
(assert (forall ((x_148 Nat_0))
	(issucc_0 (succ_0 x_148))))
(assert (forall ((x_149 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_149))))
(assert (forall ((x_150 Nat_0))
	(diseqNat_0 (succ_0 x_150) zero_0)))
(assert (forall ((x_151 Nat_0) (x_152 Nat_0))
	(=> (diseqNat_0 x_151 x_152)
	    (diseqNat_0 (succ_0 x_151) (succ_0 x_152)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_154 Nat_0) (x_155 list_0))
	(head_1 x_154 (cons_0 x_154 x_155))))
(assert (forall ((x_154 Nat_0) (x_155 list_0))
	(tail_1 x_155 (cons_0 x_154 x_155))))
(assert (isnil_0 nil_0))
(assert (forall ((x_157 Nat_0) (x_158 list_0))
	(iscons_0 (cons_0 x_157 x_158))))
(assert (forall ((x_159 Nat_0) (x_160 list_0))
	(diseqlist_0 nil_0 (cons_0 x_159 x_160))))
(assert (forall ((x_161 Nat_0) (x_162 list_0))
	(diseqlist_0 (cons_0 x_161 x_162) nil_0)))
(assert (forall ((x_163 Nat_0) (x_164 list_0) (x_165 Nat_0) (x_166 list_0))
	(=> (diseqNat_0 x_163 x_165)
	    (diseqlist_0 (cons_0 x_163 x_164) (cons_0 x_165 x_166)))))
(assert (forall ((x_163 Nat_0) (x_164 list_0) (x_165 Nat_0) (x_166 list_0))
	(=> (diseqlist_0 x_164 x_166)
	    (diseqlist_0 (cons_0 x_163 x_164) (cons_0 x_165 x_166)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_167 list_0) (x_168 list_0))
	(projpair_2 x_167 (pair_1 x_167 x_168))))
(assert (forall ((x_167 list_0) (x_168 list_0))
	(projpair_3 x_168 (pair_1 x_167 x_168))))
(assert (forall ((x_170 list_0) (x_171 list_0))
	(ispair_0 (pair_1 x_170 x_171))))
(assert (forall ((x_172 list_0) (x_173 list_0) (x_174 list_0) (x_175 list_0))
	(=> (diseqlist_0 x_172 x_174)
	    (diseqpair_0 (pair_1 x_172 x_173) (pair_1 x_174 x_175)))))
(assert (forall ((x_172 list_0) (x_173 list_0) (x_174 list_0) (x_175 list_0))
	(=> (diseqlist_0 x_173 x_175)
	    (diseqpair_0 (pair_1 x_172 x_173) (pair_1 x_174 x_175)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_38 list_0) (z_1 Nat_0) (xs_0 list_0) (z_0 Nat_0))
	(=> (take_0 x_38 z_0 xs_0)
	    (take_0 (cons_0 z_1 x_38) (succ_0 z_0) (cons_0 z_1 xs_0)))))
(assert (forall ((z_0 Nat_0))
	(take_0 nil_0 (succ_0 z_0) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 zero_0 y_0)))
(declare-fun plus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_42 Nat_0) (z_2 Nat_0) (y_1 Nat_0))
	(=> (plus_0 x_42 z_2 y_1)
	    (plus_0 (succ_0 x_42) (succ_0 z_2) y_1))))
(assert (forall ((x_43 Nat_0))
	(plus_0 x_43 zero_0 x_43)))
(declare-fun times_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_44 Nat_0) (x_45 Nat_0) (z_3 Nat_0) (y_2 Nat_0))
	(=>	(and (times_0 x_45 z_3 y_2)
			(plus_0 x_44 y_2 x_45))
		(times_0 x_44 (succ_0 z_3) y_2))))
(assert (forall ((y_2 Nat_0))
	(times_0 zero_0 zero_0 y_2)))
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_48 Nat_0) (y_4 Nat_0) (z_4 Nat_0))
	(=> (minus_0 x_48 z_4 y_4)
	    (minus_0 x_48 (succ_0 z_4) (succ_0 y_4)))))
(assert (forall ((z_4 Nat_0))
	(minus_0 zero_0 (succ_0 z_4) zero_0)))
(assert (forall ((y_3 Nat_0))
	(minus_0 zero_0 zero_0 y_3)))
(declare-fun lt_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_52 Bool_0) (n_0 Nat_0) (z_5 Nat_0))
	(=> (lt_0 x_52 n_0 z_5)
	    (lt_0 x_52 (succ_0 n_0) (succ_0 z_5)))))
(assert (forall ((z_5 Nat_0))
	(lt_0 true_0 zero_0 (succ_0 z_5))))
(assert (forall ((x_4 Nat_0))
	(lt_0 false_0 x_4 zero_0)))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_56 Bool_0) (x_6 Nat_0) (z_6 Nat_0))
	(=> (leq_0 x_56 z_6 x_6)
	    (leq_0 x_56 (succ_0 z_6) (succ_0 x_6)))))
(assert (forall ((z_6 Nat_0))
	(leq_0 false_0 (succ_0 z_6) zero_0)))
(assert (forall ((y_6 Nat_0))
	(leq_0 true_0 zero_0 y_6)))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_7 Nat_0) (y_7 Nat_0))
	(=> (leq_0 true_0 x_7 y_7)
	    (sort_0 (cons_0 x_7 (cons_0 y_7 nil_0)) x_7 y_7))))
(assert (forall ((x_62 Bool_0) (x_7 Nat_0) (y_7 Nat_0))
	(=>	(and (diseqBool_0 x_62 true_0)
			(leq_0 x_62 x_7 y_7))
		(sort_0 (cons_0 y_7 (cons_0 x_7 nil_0)) x_7 y_7))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_64 Nat_0) (x_65 Nat_0) (y_8 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_65 l_0)
			(plus_0 x_64 (succ_0 zero_0) x_65))
		(length_0 x_64 (cons_0 y_8 l_0)))))
(assert (length_0 zero_0 nil_0))
(declare-fun idiv_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_9 Nat_0) (y_9 Nat_0))
	(=> (lt_0 true_0 x_9 y_9)
	    (idiv_0 zero_0 x_9 y_9))))
(assert (forall ((x_72 Nat_0) (x_73 Nat_0) (x_70 Bool_0) (x_9 Nat_0) (y_9 Nat_0))
	(=>	(and (diseqBool_0 x_70 true_0)
			(minus_0 x_72 x_9 y_9)
			(idiv_0 x_73 x_72 y_9)
			(lt_0 x_70 x_9 y_9))
		(idiv_0 (succ_0 x_73) x_9 y_9))))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_74 list_0) (z_8 Nat_0) (xs_1 list_0) (z_7 Nat_0))
	(=> (drop_0 x_74 z_7 xs_1)
	    (drop_0 x_74 (succ_0 z_7) (cons_0 z_8 xs_1)))))
(assert (forall ((z_7 Nat_0))
	(drop_0 nil_0 (succ_0 z_7) nil_0)))
(assert (forall ((x_77 list_0))
	(drop_0 x_77 zero_0 x_77)))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_79 list_0) (x_80 list_0) (x_11 Nat_0) (y_11 list_0))
	(=>	(and (take_0 x_79 x_11 y_11)
			(drop_0 x_80 x_11 y_11))
		(splitAt_0 (pair_1 x_79 x_80) x_11 y_11))))
(declare-fun count_0 (Nat_0 Nat_0 list_0) Bool)
(assert (forall ((x_81 Nat_0) (x_82 Nat_0) (ys_0 list_0) (x_12 Nat_0))
	(=>	(and (count_0 x_82 x_12 ys_0)
			(plus_0 x_81 (succ_0 zero_0) x_82))
		(count_0 x_81 x_12 (cons_0 x_12 ys_0)))))
(assert (forall ((x_84 Nat_0) (z_9 Nat_0) (ys_0 list_0) (x_12 Nat_0))
	(=>	(and (diseqNat_0 x_12 z_9)
			(count_0 x_84 x_12 ys_0))
		(count_0 x_84 x_12 (cons_0 z_9 ys_0)))))
(assert (forall ((x_12 Nat_0))
	(count_0 zero_0 x_12 nil_0)))
(declare-fun x_13 (list_0 list_0 list_0) Bool)
(assert (forall ((x_88 list_0) (z_10 Nat_0) (xs_2 list_0) (y_13 list_0))
	(=> (x_13 x_88 xs_2 y_13)
	    (x_13 (cons_0 z_10 x_88) (cons_0 z_10 xs_2) y_13))))
(assert (forall ((x_89 list_0))
	(x_13 x_89 nil_0 x_89)))
(declare-fun stoogesort_0 (list_0 list_0) Bool)
(declare-fun stoogesort_1 (list_0 list_0) Bool)
(declare-fun stoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_94 list_0) (x_95 list_0) (x_90 Nat_0) (x_91 Nat_0) (x_92 Nat_0) (ys_1 list_0) (zs_0 list_0) (x_18 list_0))
	(=>	(and (stoogesort_1 x_95 ys_1)
			(x_13 x_94 x_95 zs_0)
			(length_0 x_90 x_18)
			(times_0 x_91 (succ_0 (succ_0 zero_0)) x_90)
			(idiv_0 x_92 (succ_0 x_91) (succ_0 (succ_0 (succ_0 zero_0))))
			(splitAt_0 (pair_1 ys_1 zs_0) x_92 x_18))
		(stoogesort_0 x_94 x_18))))
(assert (forall ((x_98 list_0) (x_99 list_0) (x_100 list_0) (x_21 Nat_0) (x_22 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=>	(and (stoogesort_0 x_98 (cons_0 y_14 (cons_0 y_15 (cons_0 x_21 x_22))))
			(stoogesort_2 x_99 x_98)
			(stoogesort_0 x_100 x_99))
		(stoogesort_1 x_100 (cons_0 y_14 (cons_0 y_15 (cons_0 x_21 x_22)))))))
(assert (forall ((x_101 list_0) (y_15 Nat_0) (y_14 Nat_0))
	(=> (sort_0 x_101 y_14 y_15)
	    (stoogesort_1 x_101 (cons_0 y_14 (cons_0 y_15 nil_0))))))
(assert (forall ((y_14 Nat_0))
	(stoogesort_1 (cons_0 y_14 nil_0) (cons_0 y_14 nil_0))))
(assert (stoogesort_1 nil_0 nil_0))
(assert (forall ((x_108 list_0) (x_109 list_0) (x_105 Nat_0) (x_106 Nat_0) (ys_2 list_0) (zs_1 list_0) (x_23 list_0))
	(=>	(and (stoogesort_1 x_109 zs_1)
			(x_13 x_108 ys_2 x_109)
			(length_0 x_105 x_23)
			(idiv_0 x_106 x_105 (succ_0 (succ_0 (succ_0 zero_0))))
			(splitAt_0 (pair_1 ys_2 zs_1) x_106 x_23))
		(stoogesort_2 x_108 x_23))))
(assert (forall ((x_111 Nat_0) (x_112 Nat_0) (x_113 Nat_0) (x_114 Nat_0) (x_24 Nat_0) (y_16 Nat_0) (z_12 Nat_0))
	(=>	(and (diseqNat_0 x_112 x_114)
			(times_0 x_111 y_16 z_12)
			(times_0 x_112 x_24 x_111)
			(times_0 x_113 x_24 y_16)
			(times_0 x_114 x_113 z_12))
		false)))
(assert (forall ((x_115 Nat_0) (x_116 Nat_0) (x_117 Nat_0) (x_118 Nat_0) (x_25 Nat_0) (y_17 Nat_0) (z_13 Nat_0))
	(=>	(and (diseqNat_0 x_116 x_118)
			(plus_0 x_115 y_17 z_13)
			(plus_0 x_116 x_25 x_115)
			(plus_0 x_117 x_25 y_17)
			(plus_0 x_118 x_117 z_13))
		false)))
(assert (forall ((x_119 Nat_0) (x_120 Nat_0) (x_26 Nat_0) (y_18 Nat_0))
	(=>	(and (diseqNat_0 x_119 x_120)
			(times_0 x_119 x_26 y_18)
			(times_0 x_120 y_18 x_26))
		false)))
(assert (forall ((x_121 Nat_0) (x_122 Nat_0) (x_27 Nat_0) (y_19 Nat_0))
	(=>	(and (diseqNat_0 x_121 x_122)
			(plus_0 x_121 x_27 y_19)
			(plus_0 x_122 y_19 x_27))
		false)))
(assert (forall ((x_123 Nat_0) (x_124 Nat_0) (x_125 Nat_0) (x_126 Nat_0) (x_127 Nat_0) (x_28 Nat_0) (y_20 Nat_0) (z_14 Nat_0))
	(=>	(and (diseqNat_0 x_124 x_127)
			(plus_0 x_123 y_20 z_14)
			(times_0 x_124 x_28 x_123)
			(times_0 x_125 x_28 y_20)
			(times_0 x_126 x_28 z_14)
			(plus_0 x_127 x_125 x_126))
		false)))
(assert (forall ((x_128 Nat_0) (x_129 Nat_0) (x_130 Nat_0) (x_131 Nat_0) (x_132 Nat_0) (x_29 Nat_0) (y_21 Nat_0) (z_15 Nat_0))
	(=>	(and (diseqNat_0 x_129 x_132)
			(plus_0 x_128 x_29 y_21)
			(times_0 x_129 x_128 z_15)
			(times_0 x_130 x_29 z_15)
			(times_0 x_131 y_21 z_15)
			(plus_0 x_132 x_130 x_131))
		false)))
(assert (forall ((x_133 Nat_0) (x_30 Nat_0))
	(=>	(and (diseqNat_0 x_133 x_30)
			(times_0 x_133 x_30 (succ_0 zero_0)))
		false)))
(assert (forall ((x_134 Nat_0) (x_31 Nat_0))
	(=>	(and (diseqNat_0 x_134 x_31)
			(times_0 x_134 (succ_0 zero_0) x_31))
		false)))
(assert (forall ((x_135 Nat_0) (x_32 Nat_0))
	(=>	(and (diseqNat_0 x_135 x_32)
			(plus_0 x_135 x_32 zero_0))
		false)))
(assert (forall ((x_136 Nat_0) (x_33 Nat_0))
	(=>	(and (diseqNat_0 x_136 x_33)
			(plus_0 x_136 zero_0 x_33))
		false)))
(assert (forall ((x_137 Nat_0) (x_34 Nat_0))
	(=>	(and (diseqNat_0 x_137 zero_0)
			(times_0 x_137 x_34 zero_0))
		false)))
(assert (forall ((x_138 Nat_0) (x_35 Nat_0))
	(=>	(and (diseqNat_0 x_138 zero_0)
			(times_0 x_138 zero_0 x_35))
		false)))
(assert (forall ((x_139 list_0) (x_140 Nat_0) (x_141 Nat_0) (x_36 Nat_0) (xs_3 list_0))
	(=>	(and (diseqNat_0 x_140 x_141)
			(stoogesort_1 x_139 xs_3)
			(count_0 x_140 x_36 x_139)
			(count_0 x_141 x_36 xs_3))
		false)))
(check-sat)
