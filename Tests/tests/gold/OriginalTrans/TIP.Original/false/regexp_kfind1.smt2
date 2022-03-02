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
(declare-fun or_1 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun hence_0 (Bool_0 Bool_0 Bool_0) Bool)
(declare-fun not_0 (Bool_0 Bool_0) Bool)
(assert (and_0 false_0 false_0 false_0))
(assert (and_0 false_0 true_0 false_0))
(assert (and_0 false_0 false_0 true_0))
(assert (and_0 true_0 true_0 true_0))
(assert (or_1 false_0 false_0 false_0))
(assert (or_1 true_0 true_0 false_0))
(assert (or_1 true_0 false_0 true_0))
(assert (or_1 true_0 true_0 true_0))
(assert (hence_0 true_0 false_0 false_0))
(assert (hence_0 false_0 true_0 false_0))
(assert (hence_0 true_0 false_0 true_0))
(assert (hence_0 true_0 true_0 true_0))
(assert (not_0 true_0 false_0))
(assert (not_0 false_0 true_0))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Bool_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_3 (Bool_0 list_0) Bool)
(declare-fun tail_3 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_98 Bool_0) (x_99 list_0))
	(head_3 x_98 (cons_0 x_98 x_99))))
(assert (forall ((x_98 Bool_0) (x_99 list_0))
	(tail_3 x_99 (cons_0 x_98 x_99))))
(assert (isnil_0 nil_0))
(assert (forall ((x_101 Bool_0) (x_102 list_0))
	(iscons_0 (cons_0 x_101 x_102))))
(assert (forall ((x_103 Bool_0) (x_104 list_0))
	(diseqlist_0 nil_0 (cons_0 x_103 x_104))))
(assert (forall ((x_105 Bool_0) (x_106 list_0))
	(diseqlist_0 (cons_0 x_105 x_106) nil_0)))
(assert (forall ((x_107 Bool_0) (x_108 list_0) (x_109 Bool_0) (x_110 list_0))
	(=> (diseqBool_0 x_107 x_109)
	    (diseqlist_0 (cons_0 x_107 x_108) (cons_0 x_109 x_110)))))
(assert (forall ((x_107 Bool_0) (x_108 list_0) (x_109 Bool_0) (x_110 list_0))
	(=> (diseqlist_0 x_108 x_110)
	    (diseqlist_0 (cons_0 x_107 x_108) (cons_0 x_109 x_110)))))
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
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 T_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_4 (T_0 list_1) Bool)
(declare-fun tail_4 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_115 T_0) (x_116 list_1))
	(head_4 x_115 (cons_1 x_115 x_116))))
(assert (forall ((x_115 T_0) (x_116 list_1))
	(tail_4 x_116 (cons_1 x_115 x_116))))
(assert (isnil_1 nil_1))
(assert (forall ((x_118 T_0) (x_119 list_1))
	(iscons_1 (cons_1 x_118 x_119))))
(assert (forall ((x_120 T_0) (x_121 list_1))
	(diseqlist_1 nil_1 (cons_1 x_120 x_121))))
(assert (forall ((x_122 T_0) (x_123 list_1))
	(diseqlist_1 (cons_1 x_122 x_123) nil_1)))
(assert (forall ((x_124 T_0) (x_125 list_1) (x_126 T_0) (x_127 list_1))
	(=> (diseqT_0 x_124 x_126)
	    (diseqlist_1 (cons_1 x_124 x_125) (cons_1 x_126 x_127)))))
(assert (forall ((x_124 T_0) (x_125 list_1) (x_126 T_0) (x_127 list_1))
	(=> (diseqlist_1 x_125 x_127)
	    (diseqlist_1 (cons_1 x_124 x_125) (cons_1 x_126 x_127)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_1) (projpair_1 list_1)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_1 pair_0) Bool)
(declare-fun projpair_3 (list_1 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_128 list_1) (x_129 list_1))
	(projpair_2 x_128 (pair_1 x_128 x_129))))
(assert (forall ((x_128 list_1) (x_129 list_1))
	(projpair_3 x_129 (pair_1 x_128 x_129))))
(assert (forall ((x_131 list_1) (x_132 list_1))
	(ispair_0 (pair_1 x_131 x_132))))
(assert (forall ((x_133 list_1) (x_134 list_1) (x_135 list_1) (x_136 list_1))
	(=> (diseqlist_1 x_133 x_135)
	    (diseqpair_0 (pair_1 x_133 x_134) (pair_1 x_135 x_136)))))
(assert (forall ((x_133 list_1) (x_134 list_1) (x_135 list_1) (x_136 list_1))
	(=> (diseqlist_1 x_134 x_136)
	    (diseqpair_0 (pair_1 x_133 x_134) (pair_1 x_135 x_136)))))
(declare-datatypes ((list_2 0)) (((nil_2 ) (cons_2 (head_2 pair_0) (tail_2 list_2)))))
(declare-fun diseqlist_2 (list_2 list_2) Bool)
(declare-fun head_5 (pair_0 list_2) Bool)
(declare-fun tail_5 (list_2 list_2) Bool)
(declare-fun isnil_2 (list_2) Bool)
(declare-fun iscons_2 (list_2) Bool)
(assert (forall ((x_138 pair_0) (x_139 list_2))
	(head_5 x_138 (cons_2 x_138 x_139))))
(assert (forall ((x_138 pair_0) (x_139 list_2))
	(tail_5 x_139 (cons_2 x_138 x_139))))
(assert (isnil_2 nil_2))
(assert (forall ((x_141 pair_0) (x_142 list_2))
	(iscons_2 (cons_2 x_141 x_142))))
(assert (forall ((x_143 pair_0) (x_144 list_2))
	(diseqlist_2 nil_2 (cons_2 x_143 x_144))))
(assert (forall ((x_145 pair_0) (x_146 list_2))
	(diseqlist_2 (cons_2 x_145 x_146) nil_2)))
(assert (forall ((x_147 pair_0) (x_148 list_2) (x_149 pair_0) (x_150 list_2))
	(=> (diseqpair_0 x_147 x_149)
	    (diseqlist_2 (cons_2 x_147 x_148) (cons_2 x_149 x_150)))))
(assert (forall ((x_147 pair_0) (x_148 list_2) (x_149 pair_0) (x_150 list_2))
	(=> (diseqlist_2 x_148 x_150)
	    (diseqlist_2 (cons_2 x_147 x_148) (cons_2 x_149 x_150)))))
(declare-datatypes ((R_0 0)) (((Nil_3 ) (Eps_0 ) (Atom_0 (projAtom_0 T_0)) (x_0 (proj_0 R_0) (proj_1 R_0)) (x_1 (proj_2 R_0) (proj_3 R_0)) (Star_0 (projStar_0 R_0)))))
(declare-fun diseqR_0 (R_0 R_0) Bool)
(declare-fun projAtom_1 (T_0 R_0) Bool)
(declare-fun proj_4 (R_0 R_0) Bool)
(declare-fun proj_5 (R_0 R_0) Bool)
(declare-fun proj_6 (R_0 R_0) Bool)
(declare-fun proj_7 (R_0 R_0) Bool)
(declare-fun projStar_1 (R_0 R_0) Bool)
(declare-fun isNil_3 (R_0) Bool)
(declare-fun isEps_0 (R_0) Bool)
(declare-fun isAtom_0 (R_0) Bool)
(declare-fun isx_0 (R_0) Bool)
(declare-fun isx_1 (R_0) Bool)
(declare-fun isStar_0 (R_0) Bool)
(assert (forall ((x_153 T_0))
	(projAtom_1 x_153 (Atom_0 x_153))))
(assert (forall ((x_155 R_0) (x_156 R_0))
	(proj_4 x_155 (x_0 x_155 x_156))))
(assert (forall ((x_155 R_0) (x_156 R_0))
	(proj_5 x_156 (x_0 x_155 x_156))))
(assert (forall ((x_158 R_0) (x_159 R_0))
	(proj_6 x_158 (x_1 x_158 x_159))))
(assert (forall ((x_158 R_0) (x_159 R_0))
	(proj_7 x_159 (x_1 x_158 x_159))))
(assert (forall ((x_161 R_0))
	(projStar_1 x_161 (Star_0 x_161))))
(assert (isNil_3 Nil_3))
(assert (isEps_0 Eps_0))
(assert (forall ((x_163 T_0))
	(isAtom_0 (Atom_0 x_163))))
(assert (forall ((x_164 R_0) (x_165 R_0))
	(isx_0 (x_0 x_164 x_165))))
(assert (forall ((x_166 R_0) (x_167 R_0))
	(isx_1 (x_1 x_166 x_167))))
(assert (forall ((x_168 R_0))
	(isStar_0 (Star_0 x_168))))
(assert (diseqR_0 Nil_3 Eps_0))
(assert (forall ((x_169 T_0))
	(diseqR_0 Nil_3 (Atom_0 x_169))))
(assert (forall ((x_170 R_0) (x_171 R_0))
	(diseqR_0 Nil_3 (x_0 x_170 x_171))))
(assert (forall ((x_172 R_0) (x_173 R_0))
	(diseqR_0 Nil_3 (x_1 x_172 x_173))))
(assert (forall ((x_174 R_0))
	(diseqR_0 Nil_3 (Star_0 x_174))))
(assert (diseqR_0 Eps_0 Nil_3))
(assert (forall ((x_175 T_0))
	(diseqR_0 (Atom_0 x_175) Nil_3)))
(assert (forall ((x_176 R_0) (x_177 R_0))
	(diseqR_0 (x_0 x_176 x_177) Nil_3)))
(assert (forall ((x_178 R_0) (x_179 R_0))
	(diseqR_0 (x_1 x_178 x_179) Nil_3)))
(assert (forall ((x_180 R_0))
	(diseqR_0 (Star_0 x_180) Nil_3)))
(assert (forall ((x_181 T_0))
	(diseqR_0 Eps_0 (Atom_0 x_181))))
(assert (forall ((x_182 R_0) (x_183 R_0))
	(diseqR_0 Eps_0 (x_0 x_182 x_183))))
(assert (forall ((x_184 R_0) (x_185 R_0))
	(diseqR_0 Eps_0 (x_1 x_184 x_185))))
(assert (forall ((x_186 R_0))
	(diseqR_0 Eps_0 (Star_0 x_186))))
(assert (forall ((x_187 T_0))
	(diseqR_0 (Atom_0 x_187) Eps_0)))
(assert (forall ((x_188 R_0) (x_189 R_0))
	(diseqR_0 (x_0 x_188 x_189) Eps_0)))
(assert (forall ((x_190 R_0) (x_191 R_0))
	(diseqR_0 (x_1 x_190 x_191) Eps_0)))
(assert (forall ((x_192 R_0))
	(diseqR_0 (Star_0 x_192) Eps_0)))
(assert (forall ((x_193 T_0) (x_194 R_0) (x_195 R_0))
	(diseqR_0 (Atom_0 x_193) (x_0 x_194 x_195))))
(assert (forall ((x_196 T_0) (x_197 R_0) (x_198 R_0))
	(diseqR_0 (Atom_0 x_196) (x_1 x_197 x_198))))
(assert (forall ((x_199 T_0) (x_200 R_0))
	(diseqR_0 (Atom_0 x_199) (Star_0 x_200))))
(assert (forall ((x_201 R_0) (x_202 R_0) (x_203 T_0))
	(diseqR_0 (x_0 x_201 x_202) (Atom_0 x_203))))
(assert (forall ((x_204 R_0) (x_205 R_0) (x_206 T_0))
	(diseqR_0 (x_1 x_204 x_205) (Atom_0 x_206))))
(assert (forall ((x_207 R_0) (x_208 T_0))
	(diseqR_0 (Star_0 x_207) (Atom_0 x_208))))
(assert (forall ((x_209 R_0) (x_210 R_0) (x_211 R_0) (x_212 R_0))
	(diseqR_0 (x_0 x_209 x_210) (x_1 x_211 x_212))))
(assert (forall ((x_213 R_0) (x_214 R_0) (x_215 R_0))
	(diseqR_0 (x_0 x_213 x_214) (Star_0 x_215))))
(assert (forall ((x_216 R_0) (x_217 R_0) (x_218 R_0) (x_219 R_0))
	(diseqR_0 (x_1 x_216 x_217) (x_0 x_218 x_219))))
(assert (forall ((x_220 R_0) (x_221 R_0) (x_222 R_0))
	(diseqR_0 (Star_0 x_220) (x_0 x_221 x_222))))
(assert (forall ((x_223 R_0) (x_224 R_0) (x_225 R_0))
	(diseqR_0 (x_1 x_223 x_224) (Star_0 x_225))))
(assert (forall ((x_226 R_0) (x_227 R_0) (x_228 R_0))
	(diseqR_0 (Star_0 x_226) (x_1 x_227 x_228))))
(assert (forall ((x_229 T_0) (x_230 T_0))
	(=> (diseqT_0 x_229 x_230)
	    (diseqR_0 (Atom_0 x_229) (Atom_0 x_230)))))
(assert (forall ((x_231 R_0) (x_232 R_0) (x_233 R_0) (x_234 R_0))
	(=> (diseqR_0 x_231 x_233)
	    (diseqR_0 (x_0 x_231 x_232) (x_0 x_233 x_234)))))
(assert (forall ((x_231 R_0) (x_232 R_0) (x_233 R_0) (x_234 R_0))
	(=> (diseqR_0 x_232 x_234)
	    (diseqR_0 (x_0 x_231 x_232) (x_0 x_233 x_234)))))
(assert (forall ((x_235 R_0) (x_236 R_0) (x_237 R_0) (x_238 R_0))
	(=> (diseqR_0 x_235 x_237)
	    (diseqR_0 (x_1 x_235 x_236) (x_1 x_237 x_238)))))
(assert (forall ((x_235 R_0) (x_236 R_0) (x_237 R_0) (x_238 R_0))
	(=> (diseqR_0 x_236 x_238)
	    (diseqR_0 (x_1 x_235 x_236) (x_1 x_237 x_238)))))
(assert (forall ((x_239 R_0) (x_240 R_0))
	(=> (diseqR_0 x_239 x_240)
	    (diseqR_0 (Star_0 x_239) (Star_0 x_240)))))
(declare-fun splits_0 (list_2 T_0 list_2) Bool)
(assert (forall ((x_23 list_2) (bs_0 list_1) (cs_0 list_1) (x_3 list_2) (x_2 T_0))
	(=> (splits_0 x_23 x_2 x_3)
	    (splits_0 (cons_2 (pair_1 (cons_1 x_2 bs_0) cs_0) x_23) x_2 (cons_2 (pair_1 bs_0 cs_0) x_3)))))
(assert (forall ((x_2 T_0))
	(splits_0 nil_2 x_2 nil_2)))
(declare-fun splits_1 (list_2 list_1) Bool)
(assert (forall ((x_26 list_2) (x_27 list_2) (y_1 T_0) (xs_0 list_1))
	(=>	(and (splits_1 x_26 xs_0)
			(splits_0 x_27 y_1 x_26))
		(splits_1 (cons_2 (pair_1 nil_1 (cons_1 y_1 xs_0)) x_27) (cons_1 y_1 xs_0)))))
(assert (splits_1 (cons_2 (pair_1 nil_1 nil_1) nil_2) nil_1))
(declare-fun or_0 (Bool_0 list_0) Bool)
(assert (forall ((x_29 Bool_0) (x_30 Bool_0) (y_2 Bool_0) (xs_1 list_0))
	(=>	(and (or_0 x_30 xs_1)
			(or_1 x_29 y_2 x_30))
		(or_0 x_29 (cons_0 y_2 xs_1)))))
(assert (or_0 false_0 nil_0))
(declare-fun eps_1 (Bool_0 R_0) Bool)
(assert (forall ((y_3 R_0))
	(eps_1 true_0 (Star_0 y_3))))
(assert (forall ((x_33 Bool_0) (x_34 Bool_0) (x_35 Bool_0) (r_1 R_0) (q_1 R_0))
	(=>	(and (eps_1 x_34 r_1)
			(eps_1 x_35 q_1)
			(and_0 x_33 x_34 x_35))
		(eps_1 x_33 (x_1 r_1 q_1)))))
(assert (forall ((x_36 Bool_0) (x_37 Bool_0) (x_38 Bool_0) (p_0 R_0) (q_0 R_0))
	(=>	(and (eps_1 x_37 p_0)
			(eps_1 x_38 q_0)
			(or_1 x_36 x_37 x_38))
		(eps_1 x_36 (x_0 p_0 q_0)))))
(assert (eps_1 true_0 Eps_0))
(assert (forall ((x_7 R_0) (x_21 T_0))
	(eps_1 false_0 (Atom_0 x_21))))
(assert (forall ((x_7 R_0))
	(eps_1 false_0 Nil_3)))
(declare-fun step_0 (R_0 R_0 T_0) Bool)
(assert (forall ((x_43 R_0) (p_2 R_0) (y_4 T_0))
	(=> (step_0 x_43 p_2 y_4)
	    (step_0 (x_1 x_43 (Star_0 p_2)) (Star_0 p_2) y_4))))
(assert (forall ((x_46 R_0) (x_47 R_0) (r_2 R_0) (q_3 R_0) (y_4 T_0))
	(=>	(and (step_0 x_46 r_2 y_4)
			(step_0 x_47 q_3 y_4)
			(eps_1 true_0 r_2))
		(step_0 (x_0 (x_1 x_46 q_3) x_47) (x_1 r_2 q_3) y_4))))
(assert (forall ((x_50 R_0) (x_48 Bool_0) (r_2 R_0) (q_3 R_0) (y_4 T_0))
	(=>	(and (diseqBool_0 x_48 true_0)
			(step_0 x_50 r_2 y_4)
			(eps_1 x_48 r_2))
		(step_0 (x_0 (x_1 x_50 q_3) Nil_3) (x_1 r_2 q_3) y_4))))
(assert (forall ((x_52 R_0) (x_53 R_0) (p_1 R_0) (q_2 R_0) (y_4 T_0))
	(=>	(and (step_0 x_52 p_1 y_4)
			(step_0 x_53 q_2 y_4))
		(step_0 (x_0 x_52 x_53) (x_0 p_1 q_2) y_4))))
(assert (forall ((b_1 T_0))
	(step_0 Eps_0 (Atom_0 b_1) b_1)))
(assert (forall ((b_1 T_0) (y_4 T_0))
	(=> (diseqT_0 b_1 y_4)
	    (step_0 Nil_3 (Atom_0 b_1) y_4))))
(assert (forall ((x_9 R_0) (y_4 T_0))
	(step_0 Nil_3 Eps_0 y_4)))
(assert (forall ((x_9 R_0) (y_4 T_0))
	(step_0 Nil_3 Nil_3 y_4)))
(declare-fun rec_0 (Bool_0 R_0 list_1) Bool)
(assert (forall ((x_58 Bool_0) (x_59 R_0) (z_1 T_0) (xs_2 list_1) (x_10 R_0))
	(=>	(and (step_0 x_59 x_10 z_1)
			(rec_0 x_58 x_59 xs_2))
		(rec_0 x_58 x_10 (cons_1 z_1 xs_2)))))
(assert (forall ((x_61 Bool_0) (x_10 R_0))
	(=> (eps_1 x_61 x_10)
	    (rec_0 x_61 x_10 nil_1))))
(declare-fun reck_0 (Bool_0 R_0 list_1) Bool)
(declare-fun reck_1 (list_0 R_0 R_0 list_2) Bool)
(assert (forall ((x_64 Bool_0) (x_63 Bool_0) (x_18 T_0) (x_19 list_1) (p_5 R_0))
	(=>	(and (diseqBool_0 x_63 true_0)
			(rec_0 x_64 (x_1 p_5 (Star_0 p_5)) (cons_1 x_18 x_19))
			(eps_1 x_63 p_5))
		(reck_0 x_64 (Star_0 p_5) (cons_1 x_18 x_19)))))
(assert (forall ((x_18 T_0) (x_19 list_1) (p_5 R_0))
	(=> (eps_1 true_0 p_5)
	    (reck_0 false_0 (Star_0 p_5) (cons_1 x_18 x_19)))))
(assert (forall ((p_5 R_0))
	(reck_0 true_0 (Star_0 p_5) nil_1)))
(assert (forall ((x_69 Bool_0) (x_70 list_2) (x_71 list_0) (r_3 R_0) (q_6 R_0) (y_7 list_1))
	(=>	(and (splits_1 x_70 y_7)
			(reck_1 x_71 r_3 q_6 x_70)
			(or_0 x_69 x_71))
		(reck_0 x_69 (x_1 r_3 q_6) y_7))))
(assert (forall ((x_73 Bool_0) (x_74 Bool_0) (x_75 Bool_0) (p_4 R_0) (q_5 R_0) (y_7 list_1))
	(=>	(and (reck_0 x_74 p_4 y_7)
			(reck_0 x_75 q_5 y_7)
			(or_1 x_73 x_74 x_75))
		(reck_0 x_73 (x_0 p_4 q_5) y_7))))
(assert (forall ((x_16 T_0) (x_17 list_1) (b_2 T_0) (c_1 T_0))
	(reck_0 false_0 (Atom_0 c_1) (cons_1 b_2 (cons_1 x_16 x_17)))))
(assert (forall ((b_2 T_0))
	(reck_0 true_0 (Atom_0 b_2) (cons_1 b_2 nil_1))))
(assert (forall ((b_2 T_0) (c_1 T_0))
	(=> (diseqT_0 c_1 b_2)
	    (reck_0 false_0 (Atom_0 c_1) (cons_1 b_2 nil_1)))))
(assert (forall ((c_1 T_0))
	(reck_0 false_0 (Atom_0 c_1) nil_1)))
(assert (forall ((z_2 T_0) (x_14 list_1))
	(reck_0 false_0 Eps_0 (cons_1 z_2 x_14))))
(assert (reck_0 true_0 Eps_0 nil_1))
(assert (forall ((y_7 list_1))
	(reck_0 false_0 Nil_3 y_7)))
(assert (forall ((x_93 Bool_0) (x_84 Bool_0) (x_85 Bool_0) (x_86 list_0) (l_0 list_1) (r_4 list_1) (z_3 list_2) (p_6 R_0) (q_7 R_0))
	(=>	(and (reck_0 x_84 p_6 l_0)
			(rec_0 x_85 q_7 r_4)
			(reck_1 x_86 p_6 q_7 z_3)
			(and_0 x_93 x_84 x_85))
		(reck_1 (cons_0 x_93 x_86) p_6 q_7 (cons_2 (pair_1 l_0 r_4) z_3)))))
(assert (forall ((p_6 R_0) (q_7 R_0))
	(reck_1 nil_0 p_6 q_7 nil_2)))
(assert (forall ((p_7 R_0))
	(=> (reck_0 true_0 p_7 (cons_1 A_0 (cons_1 B_0 (cons_1 B_0 nil_1))))
	    false)))
(check-sat)
