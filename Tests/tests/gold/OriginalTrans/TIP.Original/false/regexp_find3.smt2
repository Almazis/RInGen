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
(declare-datatypes ((T_0 0)) (((A_0 ) (B_0 ) (C_0 ))))
(declare-fun diseqT_0 (T_0 T_0) Bool)
(declare-fun isA_0 (T_0) Bool)
(declare-fun isB_0 (T_0) Bool)
(declare-fun isC_0 (T_0) Bool)
(assert (isA_0 A_0))
(assert (isB_0 B_0))
(assert (isC_0 C_0))
(assert (diseqT_0 A_0 B_0))
(assert (diseqT_0 A_0 C_0))
(assert (diseqT_0 B_0 A_0))
(assert (diseqT_0 C_0 A_0))
(assert (diseqT_0 B_0 C_0))
(assert (diseqT_0 C_0 B_0))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 T_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (T_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_49 T_0) (x_50 list_0))
	(head_1 x_49 (cons_0 x_49 x_50))))
(assert (forall ((x_49 T_0) (x_50 list_0))
	(tail_1 x_50 (cons_0 x_49 x_50))))
(assert (isnil_0 nil_0))
(assert (forall ((x_52 T_0) (x_53 list_0))
	(iscons_0 (cons_0 x_52 x_53))))
(assert (forall ((x_54 T_0) (x_55 list_0))
	(diseqlist_0 nil_0 (cons_0 x_54 x_55))))
(assert (forall ((x_56 T_0) (x_57 list_0))
	(diseqlist_0 (cons_0 x_56 x_57) nil_0)))
(assert (forall ((x_58 T_0) (x_59 list_0) (x_60 T_0) (x_61 list_0))
	(=> (diseqT_0 x_58 x_60)
	    (diseqlist_0 (cons_0 x_58 x_59) (cons_0 x_60 x_61)))))
(assert (forall ((x_58 T_0) (x_59 list_0) (x_60 T_0) (x_61 list_0))
	(=> (diseqlist_0 x_59 x_61)
	    (diseqlist_0 (cons_0 x_58 x_59) (cons_0 x_60 x_61)))))
(declare-datatypes ((R_0 0)) (((Nil_1 ) (Eps_0 ) (Atom_0 (projAtom_0 T_0)) (x_0 (proj_0 R_0) (proj_1 R_0)) (x_1 (proj_2 R_0) (proj_3 R_0)) (Star_0 (projStar_0 R_0)))))
(declare-fun diseqR_0 (R_0 R_0) Bool)
(declare-fun projAtom_1 (T_0 R_0) Bool)
(declare-fun proj_4 (R_0 R_0) Bool)
(declare-fun proj_5 (R_0 R_0) Bool)
(declare-fun proj_6 (R_0 R_0) Bool)
(declare-fun proj_7 (R_0 R_0) Bool)
(declare-fun projStar_1 (R_0 R_0) Bool)
(declare-fun isNil_1 (R_0) Bool)
(declare-fun isEps_0 (R_0) Bool)
(declare-fun isAtom_0 (R_0) Bool)
(declare-fun isx_0 (R_0) Bool)
(declare-fun isx_1 (R_0) Bool)
(declare-fun isStar_0 (R_0) Bool)
(assert (forall ((x_64 T_0))
	(projAtom_1 x_64 (Atom_0 x_64))))
(assert (forall ((x_66 R_0) (x_67 R_0))
	(proj_4 x_66 (x_0 x_66 x_67))))
(assert (forall ((x_66 R_0) (x_67 R_0))
	(proj_5 x_67 (x_0 x_66 x_67))))
(assert (forall ((x_69 R_0) (x_70 R_0))
	(proj_6 x_69 (x_1 x_69 x_70))))
(assert (forall ((x_69 R_0) (x_70 R_0))
	(proj_7 x_70 (x_1 x_69 x_70))))
(assert (forall ((x_72 R_0))
	(projStar_1 x_72 (Star_0 x_72))))
(assert (isNil_1 Nil_1))
(assert (isEps_0 Eps_0))
(assert (forall ((x_74 T_0))
	(isAtom_0 (Atom_0 x_74))))
(assert (forall ((x_75 R_0) (x_76 R_0))
	(isx_0 (x_0 x_75 x_76))))
(assert (forall ((x_77 R_0) (x_78 R_0))
	(isx_1 (x_1 x_77 x_78))))
(assert (forall ((x_79 R_0))
	(isStar_0 (Star_0 x_79))))
(assert (diseqR_0 Nil_1 Eps_0))
(assert (forall ((x_80 T_0))
	(diseqR_0 Nil_1 (Atom_0 x_80))))
(assert (forall ((x_81 R_0) (x_82 R_0))
	(diseqR_0 Nil_1 (x_0 x_81 x_82))))
(assert (forall ((x_83 R_0) (x_84 R_0))
	(diseqR_0 Nil_1 (x_1 x_83 x_84))))
(assert (forall ((x_85 R_0))
	(diseqR_0 Nil_1 (Star_0 x_85))))
(assert (diseqR_0 Eps_0 Nil_1))
(assert (forall ((x_86 T_0))
	(diseqR_0 (Atom_0 x_86) Nil_1)))
(assert (forall ((x_87 R_0) (x_88 R_0))
	(diseqR_0 (x_0 x_87 x_88) Nil_1)))
(assert (forall ((x_89 R_0) (x_90 R_0))
	(diseqR_0 (x_1 x_89 x_90) Nil_1)))
(assert (forall ((x_91 R_0))
	(diseqR_0 (Star_0 x_91) Nil_1)))
(assert (forall ((x_92 T_0))
	(diseqR_0 Eps_0 (Atom_0 x_92))))
(assert (forall ((x_93 R_0) (x_94 R_0))
	(diseqR_0 Eps_0 (x_0 x_93 x_94))))
(assert (forall ((x_95 R_0) (x_96 R_0))
	(diseqR_0 Eps_0 (x_1 x_95 x_96))))
(assert (forall ((x_97 R_0))
	(diseqR_0 Eps_0 (Star_0 x_97))))
(assert (forall ((x_98 T_0))
	(diseqR_0 (Atom_0 x_98) Eps_0)))
(assert (forall ((x_100 R_0) (x_99 R_0))
	(diseqR_0 (x_0 x_99 x_100) Eps_0)))
(assert (forall ((x_101 R_0) (x_102 R_0))
	(diseqR_0 (x_1 x_101 x_102) Eps_0)))
(assert (forall ((x_103 R_0))
	(diseqR_0 (Star_0 x_103) Eps_0)))
(assert (forall ((x_104 T_0) (x_105 R_0) (x_106 R_0))
	(diseqR_0 (Atom_0 x_104) (x_0 x_105 x_106))))
(assert (forall ((x_107 T_0) (x_108 R_0) (x_109 R_0))
	(diseqR_0 (Atom_0 x_107) (x_1 x_108 x_109))))
(assert (forall ((x_110 T_0) (x_111 R_0))
	(diseqR_0 (Atom_0 x_110) (Star_0 x_111))))
(assert (forall ((x_112 R_0) (x_113 R_0) (x_114 T_0))
	(diseqR_0 (x_0 x_112 x_113) (Atom_0 x_114))))
(assert (forall ((x_115 R_0) (x_116 R_0) (x_117 T_0))
	(diseqR_0 (x_1 x_115 x_116) (Atom_0 x_117))))
(assert (forall ((x_118 R_0) (x_119 T_0))
	(diseqR_0 (Star_0 x_118) (Atom_0 x_119))))
(assert (forall ((x_120 R_0) (x_121 R_0) (x_122 R_0) (x_123 R_0))
	(diseqR_0 (x_0 x_120 x_121) (x_1 x_122 x_123))))
(assert (forall ((x_124 R_0) (x_125 R_0) (x_126 R_0))
	(diseqR_0 (x_0 x_124 x_125) (Star_0 x_126))))
(assert (forall ((x_127 R_0) (x_128 R_0) (x_129 R_0) (x_130 R_0))
	(diseqR_0 (x_1 x_127 x_128) (x_0 x_129 x_130))))
(assert (forall ((x_131 R_0) (x_132 R_0) (x_133 R_0))
	(diseqR_0 (Star_0 x_131) (x_0 x_132 x_133))))
(assert (forall ((x_134 R_0) (x_135 R_0) (x_136 R_0))
	(diseqR_0 (x_1 x_134 x_135) (Star_0 x_136))))
(assert (forall ((x_137 R_0) (x_138 R_0) (x_139 R_0))
	(diseqR_0 (Star_0 x_137) (x_1 x_138 x_139))))
(assert (forall ((x_140 T_0) (x_141 T_0))
	(=> (diseqT_0 x_140 x_141)
	    (diseqR_0 (Atom_0 x_140) (Atom_0 x_141)))))
(assert (forall ((x_142 R_0) (x_143 R_0) (x_144 R_0) (x_145 R_0))
	(=> (diseqR_0 x_142 x_144)
	    (diseqR_0 (x_0 x_142 x_143) (x_0 x_144 x_145)))))
(assert (forall ((x_142 R_0) (x_143 R_0) (x_144 R_0) (x_145 R_0))
	(=> (diseqR_0 x_143 x_145)
	    (diseqR_0 (x_0 x_142 x_143) (x_0 x_144 x_145)))))
(assert (forall ((x_146 R_0) (x_147 R_0) (x_148 R_0) (x_149 R_0))
	(=> (diseqR_0 x_146 x_148)
	    (diseqR_0 (x_1 x_146 x_147) (x_1 x_148 x_149)))))
(assert (forall ((x_146 R_0) (x_147 R_0) (x_148 R_0) (x_149 R_0))
	(=> (diseqR_0 x_147 x_149)
	    (diseqR_0 (x_1 x_146 x_147) (x_1 x_148 x_149)))))
(assert (forall ((x_150 R_0) (x_151 R_0))
	(=> (diseqR_0 x_150 x_151)
	    (diseqR_0 (Star_0 x_150) (Star_0 x_151)))))
(declare-fun eps_1 (Bool_0 R_0) Bool)
(assert (forall ((y_0 R_0))
	(eps_1 true_0 (Star_0 y_0))))
(assert (forall ((x_40 Bool_0) (x_10 Bool_0) (x_11 Bool_0) (r_1 R_0) (q_1 R_0))
	(=>	(and (eps_1 x_10 r_1)
			(eps_1 x_11 q_1)
			(and_0 x_40 x_10 x_11))
		(eps_1 x_40 (x_1 r_1 q_1)))))
(assert (forall ((x_12 Bool_0) (x_13 Bool_0) (x_14 Bool_0) (p_0 R_0) (q_0 R_0))
	(=>	(and (eps_1 x_13 p_0)
			(eps_1 x_14 q_0)
			(or_0 x_12 x_13 x_14))
		(eps_1 x_12 (x_0 p_0 q_0)))))
(assert (eps_1 true_0 Eps_0))
(assert (forall ((x_3 R_0) (x_7 T_0))
	(eps_1 false_0 (Atom_0 x_7))))
(assert (forall ((x_3 R_0))
	(eps_1 false_0 Nil_1)))
(declare-fun step_0 (R_0 R_0 T_0) Bool)
(assert (forall ((x_19 R_0) (p_2 R_0) (y_1 T_0))
	(=> (step_0 x_19 p_2 y_1)
	    (step_0 (x_1 x_19 (Star_0 p_2)) (Star_0 p_2) y_1))))
(assert (forall ((x_22 R_0) (x_23 R_0) (r_2 R_0) (q_3 R_0) (y_1 T_0))
	(=>	(and (step_0 x_22 r_2 y_1)
			(step_0 x_23 q_3 y_1)
			(eps_1 true_0 r_2))
		(step_0 (x_0 (x_1 x_22 q_3) x_23) (x_1 r_2 q_3) y_1))))
(assert (forall ((x_26 R_0) (x_24 Bool_0) (r_2 R_0) (q_3 R_0) (y_1 T_0))
	(=>	(and (diseqBool_0 x_24 true_0)
			(step_0 x_26 r_2 y_1)
			(eps_1 x_24 r_2))
		(step_0 (x_0 (x_1 x_26 q_3) Nil_1) (x_1 r_2 q_3) y_1))))
(assert (forall ((x_28 R_0) (x_29 R_0) (p_1 R_0) (q_2 R_0) (y_1 T_0))
	(=>	(and (step_0 x_28 p_1 y_1)
			(step_0 x_29 q_2 y_1))
		(step_0 (x_0 x_28 x_29) (x_0 p_1 q_2) y_1))))
(assert (forall ((b_1 T_0))
	(step_0 Eps_0 (Atom_0 b_1) b_1)))
(assert (forall ((b_1 T_0) (y_1 T_0))
	(=> (diseqT_0 b_1 y_1)
	    (step_0 Nil_1 (Atom_0 b_1) y_1))))
(assert (forall ((x_5 R_0) (y_1 T_0))
	(step_0 Nil_1 Eps_0 y_1)))
(assert (forall ((x_5 R_0) (y_1 T_0))
	(step_0 Nil_1 Nil_1 y_1)))
(declare-fun rec_0 (Bool_0 R_0 list_0) Bool)
(assert (forall ((x_34 Bool_0) (x_35 R_0) (z_0 T_0) (xs_0 list_0) (x_6 R_0))
	(=>	(and (step_0 x_35 x_6 z_0)
			(rec_0 x_34 x_35 xs_0))
		(rec_0 x_34 x_6 (cons_0 z_0 xs_0)))))
(assert (forall ((x_37 Bool_0) (x_6 R_0))
	(=> (eps_1 x_37 x_6)
	    (rec_0 x_37 x_6 nil_0))))
(assert (forall ((p_3 R_0))
	(=> (rec_0 true_0 p_3 (cons_0 A_0 (cons_0 A_0 (cons_0 B_0 (cons_0 B_0 nil_0)))))
	    false)))
(check-sat)
