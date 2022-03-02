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
(assert (forall ((x_2110 Bool_0) (x_2111 list_0))
	(head_3 x_2110 (cons_0 x_2110 x_2111))))
(assert (forall ((x_2110 Bool_0) (x_2111 list_0))
	(tail_3 x_2111 (cons_0 x_2110 x_2111))))
(assert (isnil_0 nil_0))
(assert (forall ((x_2113 Bool_0) (x_2114 list_0))
	(iscons_0 (cons_0 x_2113 x_2114))))
(assert (forall ((x_2115 Bool_0) (x_2116 list_0))
	(diseqlist_0 nil_0 (cons_0 x_2115 x_2116))))
(assert (forall ((x_2117 Bool_0) (x_2118 list_0))
	(diseqlist_0 (cons_0 x_2117 x_2118) nil_0)))
(assert (forall ((x_2119 Bool_0) (x_2120 list_0) (x_2121 Bool_0) (x_2122 list_0))
	(=> (diseqBool_0 x_2119 x_2121)
	    (diseqlist_0 (cons_0 x_2119 x_2120) (cons_0 x_2121 x_2122)))))
(assert (forall ((x_2119 Bool_0) (x_2120 list_0) (x_2121 Bool_0) (x_2122 list_0))
	(=> (diseqlist_0 x_2120 x_2122)
	    (diseqlist_0 (cons_0 x_2119 x_2120) (cons_0 x_2121 x_2122)))))
(declare-datatypes ((A_0 0)) (((X_0 ) (Y_0 ))))
(declare-fun diseqA_0 (A_0 A_0) Bool)
(declare-fun isX_0 (A_0) Bool)
(declare-fun isY_0 (A_0) Bool)
(assert (isX_0 X_0))
(assert (isY_0 Y_0))
(assert (diseqA_0 X_0 Y_0))
(assert (diseqA_0 Y_0 X_0))
(declare-datatypes ((R_0 0)) (((Nil_1 ) (Eps_0 ) (Atom_0 (projAtom_0 A_0)) (Plus_0 (projPlus_0 R_0) (projPlus_1 R_0)) (Seq_0 (projSeq_0 R_0) (projSeq_1 R_0)) (Star_0 (projStar_0 R_0)))))
(declare-fun diseqR_0 (R_0 R_0) Bool)
(declare-fun projAtom_1 (A_0 R_0) Bool)
(declare-fun projPlus_2 (R_0 R_0) Bool)
(declare-fun projPlus_3 (R_0 R_0) Bool)
(declare-fun projSeq_2 (R_0 R_0) Bool)
(declare-fun projSeq_3 (R_0 R_0) Bool)
(declare-fun projStar_1 (R_0 R_0) Bool)
(declare-fun isNil_1 (R_0) Bool)
(declare-fun isEps_0 (R_0) Bool)
(declare-fun isAtom_0 (R_0) Bool)
(declare-fun isPlus_0 (R_0) Bool)
(declare-fun isSeq_0 (R_0) Bool)
(declare-fun isStar_0 (R_0) Bool)
(assert (forall ((x_2127 A_0))
	(projAtom_1 x_2127 (Atom_0 x_2127))))
(assert (forall ((x_2129 R_0) (x_2130 R_0))
	(projPlus_2 x_2129 (Plus_0 x_2129 x_2130))))
(assert (forall ((x_2129 R_0) (x_2130 R_0))
	(projPlus_3 x_2130 (Plus_0 x_2129 x_2130))))
(assert (forall ((x_2132 R_0) (x_2133 R_0))
	(projSeq_2 x_2132 (Seq_0 x_2132 x_2133))))
(assert (forall ((x_2132 R_0) (x_2133 R_0))
	(projSeq_3 x_2133 (Seq_0 x_2132 x_2133))))
(assert (forall ((x_2135 R_0))
	(projStar_1 x_2135 (Star_0 x_2135))))
(assert (isNil_1 Nil_1))
(assert (isEps_0 Eps_0))
(assert (forall ((x_2137 A_0))
	(isAtom_0 (Atom_0 x_2137))))
(assert (forall ((x_2138 R_0) (x_2139 R_0))
	(isPlus_0 (Plus_0 x_2138 x_2139))))
(assert (forall ((x_2140 R_0) (x_2141 R_0))
	(isSeq_0 (Seq_0 x_2140 x_2141))))
(assert (forall ((x_2142 R_0))
	(isStar_0 (Star_0 x_2142))))
(assert (diseqR_0 Nil_1 Eps_0))
(assert (forall ((x_2143 A_0))
	(diseqR_0 Nil_1 (Atom_0 x_2143))))
(assert (forall ((x_2144 R_0) (x_2145 R_0))
	(diseqR_0 Nil_1 (Plus_0 x_2144 x_2145))))
(assert (forall ((x_2146 R_0) (x_2147 R_0))
	(diseqR_0 Nil_1 (Seq_0 x_2146 x_2147))))
(assert (forall ((x_2148 R_0))
	(diseqR_0 Nil_1 (Star_0 x_2148))))
(assert (diseqR_0 Eps_0 Nil_1))
(assert (forall ((x_2149 A_0))
	(diseqR_0 (Atom_0 x_2149) Nil_1)))
(assert (forall ((x_2150 R_0) (x_2151 R_0))
	(diseqR_0 (Plus_0 x_2150 x_2151) Nil_1)))
(assert (forall ((x_2152 R_0) (x_2153 R_0))
	(diseqR_0 (Seq_0 x_2152 x_2153) Nil_1)))
(assert (forall ((x_2154 R_0))
	(diseqR_0 (Star_0 x_2154) Nil_1)))
(assert (forall ((x_2155 A_0))
	(diseqR_0 Eps_0 (Atom_0 x_2155))))
(assert (forall ((x_2156 R_0) (x_2157 R_0))
	(diseqR_0 Eps_0 (Plus_0 x_2156 x_2157))))
(assert (forall ((x_2158 R_0) (x_2159 R_0))
	(diseqR_0 Eps_0 (Seq_0 x_2158 x_2159))))
(assert (forall ((x_2160 R_0))
	(diseqR_0 Eps_0 (Star_0 x_2160))))
(assert (forall ((x_2161 A_0))
	(diseqR_0 (Atom_0 x_2161) Eps_0)))
(assert (forall ((x_2162 R_0) (x_2163 R_0))
	(diseqR_0 (Plus_0 x_2162 x_2163) Eps_0)))
(assert (forall ((x_2164 R_0) (x_2165 R_0))
	(diseqR_0 (Seq_0 x_2164 x_2165) Eps_0)))
(assert (forall ((x_2166 R_0))
	(diseqR_0 (Star_0 x_2166) Eps_0)))
(assert (forall ((x_2167 A_0) (x_2168 R_0) (x_2169 R_0))
	(diseqR_0 (Atom_0 x_2167) (Plus_0 x_2168 x_2169))))
(assert (forall ((x_2170 A_0) (x_2171 R_0) (x_2172 R_0))
	(diseqR_0 (Atom_0 x_2170) (Seq_0 x_2171 x_2172))))
(assert (forall ((x_2173 A_0) (x_2174 R_0))
	(diseqR_0 (Atom_0 x_2173) (Star_0 x_2174))))
(assert (forall ((x_2175 R_0) (x_2176 R_0) (x_2177 A_0))
	(diseqR_0 (Plus_0 x_2175 x_2176) (Atom_0 x_2177))))
(assert (forall ((x_2178 R_0) (x_2179 R_0) (x_2180 A_0))
	(diseqR_0 (Seq_0 x_2178 x_2179) (Atom_0 x_2180))))
(assert (forall ((x_2181 R_0) (x_2182 A_0))
	(diseqR_0 (Star_0 x_2181) (Atom_0 x_2182))))
(assert (forall ((x_2183 R_0) (x_2184 R_0) (x_2185 R_0) (x_2186 R_0))
	(diseqR_0 (Plus_0 x_2183 x_2184) (Seq_0 x_2185 x_2186))))
(assert (forall ((x_2187 R_0) (x_2188 R_0) (x_2189 R_0))
	(diseqR_0 (Plus_0 x_2187 x_2188) (Star_0 x_2189))))
(assert (forall ((x_2190 R_0) (x_2191 R_0) (x_2192 R_0) (x_2193 R_0))
	(diseqR_0 (Seq_0 x_2190 x_2191) (Plus_0 x_2192 x_2193))))
(assert (forall ((x_2194 R_0) (x_2195 R_0) (x_2196 R_0))
	(diseqR_0 (Star_0 x_2194) (Plus_0 x_2195 x_2196))))
(assert (forall ((x_2197 R_0) (x_2198 R_0) (x_2199 R_0))
	(diseqR_0 (Seq_0 x_2197 x_2198) (Star_0 x_2199))))
(assert (forall ((x_2200 R_0) (x_2201 R_0) (x_2202 R_0))
	(diseqR_0 (Star_0 x_2200) (Seq_0 x_2201 x_2202))))
(assert (forall ((x_2203 A_0) (x_2204 A_0))
	(=> (diseqA_0 x_2203 x_2204)
	    (diseqR_0 (Atom_0 x_2203) (Atom_0 x_2204)))))
(assert (forall ((x_2205 R_0) (x_2206 R_0) (x_2207 R_0) (x_2208 R_0))
	(=> (diseqR_0 x_2205 x_2207)
	    (diseqR_0 (Plus_0 x_2205 x_2206) (Plus_0 x_2207 x_2208)))))
(assert (forall ((x_2205 R_0) (x_2206 R_0) (x_2207 R_0) (x_2208 R_0))
	(=> (diseqR_0 x_2206 x_2208)
	    (diseqR_0 (Plus_0 x_2205 x_2206) (Plus_0 x_2207 x_2208)))))
(assert (forall ((x_2209 R_0) (x_2210 R_0) (x_2211 R_0) (x_2212 R_0))
	(=> (diseqR_0 x_2209 x_2211)
	    (diseqR_0 (Seq_0 x_2209 x_2210) (Seq_0 x_2211 x_2212)))))
(assert (forall ((x_2209 R_0) (x_2210 R_0) (x_2211 R_0) (x_2212 R_0))
	(=> (diseqR_0 x_2210 x_2212)
	    (diseqR_0 (Seq_0 x_2209 x_2210) (Seq_0 x_2211 x_2212)))))
(assert (forall ((x_2213 R_0) (x_2214 R_0))
	(=> (diseqR_0 x_2213 x_2214)
	    (diseqR_0 (Star_0 x_2213) (Star_0 x_2214)))))
(declare-datatypes ((list_1 0)) (((nil_2 ) (cons_1 (head_1 A_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_4 (A_0 list_1) Bool)
(declare-fun tail_4 (list_1 list_1) Bool)
(declare-fun isnil_2 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_2216 A_0) (x_2217 list_1))
	(head_4 x_2216 (cons_1 x_2216 x_2217))))
(assert (forall ((x_2216 A_0) (x_2217 list_1))
	(tail_4 x_2217 (cons_1 x_2216 x_2217))))
(assert (isnil_2 nil_2))
(assert (forall ((x_2219 A_0) (x_2220 list_1))
	(iscons_1 (cons_1 x_2219 x_2220))))
(assert (forall ((x_2221 A_0) (x_2222 list_1))
	(diseqlist_1 nil_2 (cons_1 x_2221 x_2222))))
(assert (forall ((x_2223 A_0) (x_2224 list_1))
	(diseqlist_1 (cons_1 x_2223 x_2224) nil_2)))
(assert (forall ((x_2225 A_0) (x_2226 list_1) (x_2227 A_0) (x_2228 list_1))
	(=> (diseqA_0 x_2225 x_2227)
	    (diseqlist_1 (cons_1 x_2225 x_2226) (cons_1 x_2227 x_2228)))))
(assert (forall ((x_2225 A_0) (x_2226 list_1) (x_2227 A_0) (x_2228 list_1))
	(=> (diseqlist_1 x_2226 x_2228)
	    (diseqlist_1 (cons_1 x_2225 x_2226) (cons_1 x_2227 x_2228)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_1) (projpair_1 list_1)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_1 pair_0) Bool)
(declare-fun projpair_3 (list_1 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_2229 list_1) (x_2230 list_1))
	(projpair_2 x_2229 (pair_1 x_2229 x_2230))))
(assert (forall ((x_2229 list_1) (x_2230 list_1))
	(projpair_3 x_2230 (pair_1 x_2229 x_2230))))
(assert (forall ((x_2232 list_1) (x_2233 list_1))
	(ispair_0 (pair_1 x_2232 x_2233))))
(assert (forall ((x_2234 list_1) (x_2235 list_1) (x_2236 list_1) (x_2237 list_1))
	(=> (diseqlist_1 x_2234 x_2236)
	    (diseqpair_0 (pair_1 x_2234 x_2235) (pair_1 x_2236 x_2237)))))
(assert (forall ((x_2234 list_1) (x_2235 list_1) (x_2236 list_1) (x_2237 list_1))
	(=> (diseqlist_1 x_2235 x_2237)
	    (diseqpair_0 (pair_1 x_2234 x_2235) (pair_1 x_2236 x_2237)))))
(declare-datatypes ((list_2 0)) (((nil_3 ) (cons_2 (head_2 pair_0) (tail_2 list_2)))))
(declare-fun diseqlist_2 (list_2 list_2) Bool)
(declare-fun head_5 (pair_0 list_2) Bool)
(declare-fun tail_5 (list_2 list_2) Bool)
(declare-fun isnil_3 (list_2) Bool)
(declare-fun iscons_2 (list_2) Bool)
(assert (forall ((x_2239 pair_0) (x_2240 list_2))
	(head_5 x_2239 (cons_2 x_2239 x_2240))))
(assert (forall ((x_2239 pair_0) (x_2240 list_2))
	(tail_5 x_2240 (cons_2 x_2239 x_2240))))
(assert (isnil_3 nil_3))
(assert (forall ((x_2242 pair_0) (x_2243 list_2))
	(iscons_2 (cons_2 x_2242 x_2243))))
(assert (forall ((x_2244 pair_0) (x_2245 list_2))
	(diseqlist_2 nil_3 (cons_2 x_2244 x_2245))))
(assert (forall ((x_2246 pair_0) (x_2247 list_2))
	(diseqlist_2 (cons_2 x_2246 x_2247) nil_3)))
(assert (forall ((x_2248 pair_0) (x_2249 list_2) (x_2250 pair_0) (x_2251 list_2))
	(=> (diseqpair_0 x_2248 x_2250)
	    (diseqlist_2 (cons_2 x_2248 x_2249) (cons_2 x_2250 x_2251)))))
(assert (forall ((x_2248 pair_0) (x_2249 list_2) (x_2250 pair_0) (x_2251 list_2))
	(=> (diseqlist_2 x_2249 x_2251)
	    (diseqlist_2 (cons_2 x_2248 x_2249) (cons_2 x_2250 x_2251)))))
(declare-fun split_0 (list_2 A_0 list_2) Bool)
(assert (forall ((x_1229 list_2) (xs_0 list_1) (ys_0 list_1) (x_2 list_2) (x_1 A_0))
	(=> (split_0 x_1229 x_1 x_2)
	    (split_0 (cons_2 (pair_1 (cons_1 x_1 xs_0) ys_0) x_1229) x_1 (cons_2 (pair_1 xs_0 ys_0) x_2)))))
(assert (forall ((x_1 A_0))
	(split_0 nil_3 x_1 nil_3)))
(declare-fun split_1 (list_2 list_1) Bool)
(assert (forall ((x_1232 list_2) (x_1233 list_2) (y_2 A_0) (s_0 list_1))
	(=>	(and (split_1 x_1232 s_0)
			(split_0 x_1233 y_2 x_1232))
		(split_1 (cons_2 (pair_1 nil_2 (cons_1 y_2 s_0)) x_1233) (cons_1 y_2 s_0)))))
(assert (split_1 (cons_2 (pair_1 nil_2 nil_2) nil_3) nil_2))
(declare-fun seq_1 (R_0 R_0 R_0) Bool)
(assert (forall ((y_3 R_0))
	(seq_1 Nil_1 Nil_1 y_3)))
(assert (forall ((x_5 R_0) (x_249 A_0))
	(seq_1 Nil_1 (Atom_0 x_249) Nil_1)))
(assert (forall ((x_5 R_0))
	(seq_1 Nil_1 Eps_0 Nil_1)))
(assert (forall ((x_5 R_0) (x_250 R_0) (x_251 R_0))
	(seq_1 Nil_1 (Plus_0 x_250 x_251) Nil_1)))
(assert (forall ((x_5 R_0) (x_252 R_0) (x_253 R_0))
	(seq_1 Nil_1 (Seq_0 x_252 x_253) Nil_1)))
(assert (forall ((x_5 R_0) (x_254 R_0))
	(seq_1 Nil_1 (Star_0 x_254) Nil_1)))
(assert (forall ((x_6 R_0) (x_63 A_0) (x_5 R_0))
	(seq_1 (Atom_0 x_63) Eps_0 (Atom_0 x_63))))
(assert (forall ((x_6 R_0) (x_5 R_0))
	(seq_1 Eps_0 Eps_0 Eps_0)))
(assert (forall ((x_6 R_0) (x_64 R_0) (x_65 R_0) (x_5 R_0))
	(seq_1 (Plus_0 x_64 x_65) Eps_0 (Plus_0 x_64 x_65))))
(assert (forall ((x_6 R_0) (x_66 R_0) (x_67 R_0) (x_5 R_0))
	(seq_1 (Seq_0 x_66 x_67) Eps_0 (Seq_0 x_66 x_67))))
(assert (forall ((x_6 R_0) (x_68 R_0) (x_5 R_0))
	(seq_1 (Star_0 x_68) Eps_0 (Star_0 x_68))))
(assert (forall ((x_7 R_0) (x_27 A_0) (x_6 R_0) (x_5 R_0))
	(seq_1 (Atom_0 x_27) (Atom_0 x_27) Eps_0)))
(assert (forall ((x_7 R_0) (x_28 R_0) (x_29 R_0) (x_6 R_0) (x_5 R_0))
	(seq_1 (Plus_0 x_28 x_29) (Plus_0 x_28 x_29) Eps_0)))
(assert (forall ((x_7 R_0) (x_30 R_0) (x_31 R_0) (x_6 R_0) (x_5 R_0))
	(seq_1 (Seq_0 x_30 x_31) (Seq_0 x_30 x_31) Eps_0)))
(assert (forall ((x_7 R_0) (x_32 R_0) (x_6 R_0) (x_5 R_0))
	(seq_1 (Star_0 x_32) (Star_0 x_32) Eps_0)))
(assert (forall ((x_8 R_0) (x_21 A_0) (x_7 R_0) (x_33 A_0) (x_6 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Atom_0 x_33) (Atom_0 x_21)) (Atom_0 x_33) (Atom_0 x_21))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_34 R_0) (x_35 R_0) (x_6 R_0) (x_111 A_0) (x_5 R_0))
	(seq_1 (Seq_0 (Plus_0 x_34 x_35) (Atom_0 x_111)) (Plus_0 x_34 x_35) (Atom_0 x_111))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_36 R_0) (x_37 R_0) (x_6 R_0) (x_117 A_0) (x_5 R_0))
	(seq_1 (Seq_0 (Seq_0 x_36 x_37) (Atom_0 x_117)) (Seq_0 x_36 x_37) (Atom_0 x_117))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_38 R_0) (x_6 R_0) (x_123 A_0) (x_5 R_0))
	(seq_1 (Seq_0 (Star_0 x_38) (Atom_0 x_123)) (Star_0 x_38) (Atom_0 x_123))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_45 A_0) (x_6 R_0) (x_160 R_0) (x_161 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Atom_0 x_45) (Plus_0 x_160 x_161)) (Atom_0 x_45) (Plus_0 x_160 x_161))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_46 R_0) (x_47 R_0) (x_6 R_0) (x_172 R_0) (x_173 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Plus_0 x_46 x_47) (Plus_0 x_172 x_173)) (Plus_0 x_46 x_47) (Plus_0 x_172 x_173))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_48 R_0) (x_49 R_0) (x_6 R_0) (x_178 R_0) (x_179 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Seq_0 x_48 x_49) (Plus_0 x_178 x_179)) (Seq_0 x_48 x_49) (Plus_0 x_178 x_179))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_50 R_0) (x_6 R_0) (x_184 R_0) (x_185 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Star_0 x_50) (Plus_0 x_184 x_185)) (Star_0 x_50) (Plus_0 x_184 x_185))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_51 A_0) (x_6 R_0) (x_192 R_0) (x_193 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Atom_0 x_51) (Seq_0 x_192 x_193)) (Atom_0 x_51) (Seq_0 x_192 x_193))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_52 R_0) (x_53 R_0) (x_6 R_0) (x_204 R_0) (x_205 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Plus_0 x_52 x_53) (Seq_0 x_204 x_205)) (Plus_0 x_52 x_53) (Seq_0 x_204 x_205))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_54 R_0) (x_55 R_0) (x_6 R_0) (x_210 R_0) (x_211 R_0) (x_5 R_0))
	(seq_1 (Seq_0 (Seq_0 x_54 x_55) (Seq_0 x_210 x_211)) (Seq_0 x_54 x_55) (Seq_0 x_210 x_211))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_6 R_0) (x_216 R_0) (x_217 R_0) (x_5 R_0) (x_1028 R_0))
	(seq_1 (Seq_0 (Star_0 x_1028) (Seq_0 x_216 x_217)) (Star_0 x_1028) (Seq_0 x_216 x_217))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_6 R_0) (x_224 R_0) (x_5 R_0) (x_1059 A_0))
	(seq_1 (Seq_0 (Atom_0 x_1059) (Star_0 x_224)) (Atom_0 x_1059) (Star_0 x_224))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_6 R_0) (x_236 R_0) (x_5 R_0) (x_1120 R_0) (x_1121 R_0))
	(seq_1 (Seq_0 (Plus_0 x_1120 x_1121) (Star_0 x_236)) (Plus_0 x_1120 x_1121) (Star_0 x_236))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_6 R_0) (x_242 R_0) (x_5 R_0) (x_1152 R_0) (x_1153 R_0))
	(seq_1 (Seq_0 (Seq_0 x_1152 x_1153) (Star_0 x_242)) (Seq_0 x_1152 x_1153) (Star_0 x_242))))
(assert (forall ((x_8 R_0) (x_7 R_0) (x_6 R_0) (x_248 R_0) (x_5 R_0) (x_1184 R_0))
	(seq_1 (Seq_0 (Star_0 x_1184) (Star_0 x_248)) (Star_0 x_1184) (Star_0 x_248))))
(declare-fun plus_1 (R_0 R_0 R_0) Bool)
(assert (forall ((x_2016 R_0))
	(plus_1 x_2016 Nil_1 x_2016)))
(assert (forall ((x_10 R_0) (x_1191 A_0))
	(plus_1 (Atom_0 x_1191) (Atom_0 x_1191) Nil_1)))
(assert (forall ((x_10 R_0))
	(plus_1 Eps_0 Eps_0 Nil_1)))
(assert (forall ((x_10 R_0) (x_1192 R_0) (x_1193 R_0))
	(plus_1 (Plus_0 x_1192 x_1193) (Plus_0 x_1192 x_1193) Nil_1)))
(assert (forall ((x_10 R_0) (x_1194 R_0) (x_1195 R_0))
	(plus_1 (Seq_0 x_1194 x_1195) (Seq_0 x_1194 x_1195) Nil_1)))
(assert (forall ((x_10 R_0) (x_1196 R_0))
	(plus_1 (Star_0 x_1196) (Star_0 x_1196) Nil_1)))
(assert (forall ((x_11 R_0) (x_1185 A_0) (x_10 R_0) (x_1197 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1197) (Atom_0 x_1185)) (Atom_0 x_1197) (Atom_0 x_1185))))
(assert (forall ((x_11 R_0) (x_1185 A_0) (x_10 R_0))
	(plus_1 (Plus_0 Eps_0 (Atom_0 x_1185)) Eps_0 (Atom_0 x_1185))))
(assert (forall ((x_11 R_0) (x_1185 A_0) (x_10 R_0) (x_1198 R_0) (x_1199 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1198 x_1199) (Atom_0 x_1185)) (Plus_0 x_1198 x_1199) (Atom_0 x_1185))))
(assert (forall ((x_11 R_0) (x_1185 A_0) (x_10 R_0) (x_1200 R_0) (x_1201 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1200 x_1201) (Atom_0 x_1185)) (Seq_0 x_1200 x_1201) (Atom_0 x_1185))))
(assert (forall ((x_11 R_0) (x_1185 A_0) (x_10 R_0) (x_1202 R_0))
	(plus_1 (Plus_0 (Star_0 x_1202) (Atom_0 x_1185)) (Star_0 x_1202) (Atom_0 x_1185))))
(assert (forall ((x_11 R_0) (x_10 R_0) (x_1203 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1203) Eps_0) (Atom_0 x_1203) Eps_0)))
(assert (forall ((x_11 R_0) (x_10 R_0))
	(plus_1 (Plus_0 Eps_0 Eps_0) Eps_0 Eps_0)))
(assert (forall ((x_11 R_0) (x_10 R_0) (x_1204 R_0) (x_1205 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1204 x_1205) Eps_0) (Plus_0 x_1204 x_1205) Eps_0)))
(assert (forall ((x_11 R_0) (x_10 R_0) (x_1206 R_0) (x_1207 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1206 x_1207) Eps_0) (Seq_0 x_1206 x_1207) Eps_0)))
(assert (forall ((x_11 R_0) (x_10 R_0) (x_1208 R_0))
	(plus_1 (Plus_0 (Star_0 x_1208) Eps_0) (Star_0 x_1208) Eps_0)))
(assert (forall ((x_11 R_0) (x_1186 R_0) (x_1187 R_0) (x_10 R_0) (x_1209 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1209) (Plus_0 x_1186 x_1187)) (Atom_0 x_1209) (Plus_0 x_1186 x_1187))))
(assert (forall ((x_11 R_0) (x_1186 R_0) (x_1187 R_0) (x_10 R_0))
	(plus_1 (Plus_0 Eps_0 (Plus_0 x_1186 x_1187)) Eps_0 (Plus_0 x_1186 x_1187))))
(assert (forall ((x_11 R_0) (x_1186 R_0) (x_1187 R_0) (x_10 R_0) (x_1210 R_0) (x_1211 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1210 x_1211) (Plus_0 x_1186 x_1187)) (Plus_0 x_1210 x_1211) (Plus_0 x_1186 x_1187))))
(assert (forall ((x_11 R_0) (x_1186 R_0) (x_1187 R_0) (x_10 R_0) (x_1212 R_0) (x_1213 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1212 x_1213) (Plus_0 x_1186 x_1187)) (Seq_0 x_1212 x_1213) (Plus_0 x_1186 x_1187))))
(assert (forall ((x_11 R_0) (x_1186 R_0) (x_1187 R_0) (x_10 R_0) (x_1214 R_0))
	(plus_1 (Plus_0 (Star_0 x_1214) (Plus_0 x_1186 x_1187)) (Star_0 x_1214) (Plus_0 x_1186 x_1187))))
(assert (forall ((x_11 R_0) (x_1188 R_0) (x_1189 R_0) (x_10 R_0) (x_1215 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1215) (Seq_0 x_1188 x_1189)) (Atom_0 x_1215) (Seq_0 x_1188 x_1189))))
(assert (forall ((x_11 R_0) (x_1188 R_0) (x_1189 R_0) (x_10 R_0))
	(plus_1 (Plus_0 Eps_0 (Seq_0 x_1188 x_1189)) Eps_0 (Seq_0 x_1188 x_1189))))
(assert (forall ((x_11 R_0) (x_1188 R_0) (x_1189 R_0) (x_10 R_0) (x_1216 R_0) (x_1217 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1216 x_1217) (Seq_0 x_1188 x_1189)) (Plus_0 x_1216 x_1217) (Seq_0 x_1188 x_1189))))
(assert (forall ((x_11 R_0) (x_1188 R_0) (x_1189 R_0) (x_10 R_0) (x_1218 R_0) (x_1219 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1218 x_1219) (Seq_0 x_1188 x_1189)) (Seq_0 x_1218 x_1219) (Seq_0 x_1188 x_1189))))
(assert (forall ((x_11 R_0) (x_1188 R_0) (x_1189 R_0) (x_10 R_0) (x_1220 R_0))
	(plus_1 (Plus_0 (Star_0 x_1220) (Seq_0 x_1188 x_1189)) (Star_0 x_1220) (Seq_0 x_1188 x_1189))))
(assert (forall ((x_11 R_0) (x_1190 R_0) (x_10 R_0) (x_1221 A_0))
	(plus_1 (Plus_0 (Atom_0 x_1221) (Star_0 x_1190)) (Atom_0 x_1221) (Star_0 x_1190))))
(assert (forall ((x_11 R_0) (x_1190 R_0) (x_10 R_0))
	(plus_1 (Plus_0 Eps_0 (Star_0 x_1190)) Eps_0 (Star_0 x_1190))))
(assert (forall ((x_11 R_0) (x_1190 R_0) (x_10 R_0) (x_1222 R_0) (x_1223 R_0))
	(plus_1 (Plus_0 (Plus_0 x_1222 x_1223) (Star_0 x_1190)) (Plus_0 x_1222 x_1223) (Star_0 x_1190))))
(assert (forall ((x_11 R_0) (x_1190 R_0) (x_10 R_0) (x_1224 R_0) (x_1225 R_0))
	(plus_1 (Plus_0 (Seq_0 x_1224 x_1225) (Star_0 x_1190)) (Seq_0 x_1224 x_1225) (Star_0 x_1190))))
(assert (forall ((x_11 R_0) (x_1190 R_0) (x_10 R_0) (x_1226 R_0))
	(plus_1 (Plus_0 (Star_0 x_1226) (Star_0 x_1190)) (Star_0 x_1226) (Star_0 x_1190))))
(declare-fun or_0 (Bool_0 list_0) Bool)
(assert (forall ((x_2047 Bool_0) (x_2048 Bool_0) (y_5 Bool_0) (xs_1 list_0))
	(=>	(and (or_0 x_2048 xs_1)
			(or_1 x_2047 y_5 x_2048))
		(or_0 x_2047 (cons_0 y_5 xs_1)))))
(assert (or_0 false_0 nil_0))
(declare-fun eqA_0 (Bool_0 A_0 A_0) Bool)
(assert (eqA_0 true_0 Y_0 Y_0))
(assert (eqA_0 false_0 Y_0 X_0))
(assert (eqA_0 false_0 X_0 Y_0))
(assert (eqA_0 true_0 X_0 X_0))
(declare-fun eps_1 (Bool_0 R_0) Bool)
(assert (forall ((y_7 R_0))
	(eps_1 true_0 (Star_0 y_7))))
(assert (forall ((x_2055 Bool_0) (x_2056 Bool_0) (x_2057 Bool_0) (r_1 R_0) (q_1 R_0))
	(=>	(and (eps_1 x_2056 r_1)
			(eps_1 x_2057 q_1)
			(and_0 x_2055 x_2056 x_2057))
		(eps_1 x_2055 (Seq_0 r_1 q_1)))))
(assert (forall ((x_2058 Bool_0) (x_2059 Bool_0) (x_2060 Bool_0) (p_0 R_0) (q_0 R_0))
	(=>	(and (eps_1 x_2059 p_0)
			(eps_1 x_2060 q_0)
			(or_1 x_2058 x_2059 x_2060))
		(eps_1 x_2058 (Plus_0 p_0 q_0)))))
(assert (eps_1 true_0 Eps_0))
(assert (forall ((x_15 R_0) (x_1227 A_0))
	(eps_1 false_0 (Atom_0 x_1227))))
(assert (forall ((x_15 R_0))
	(eps_1 false_0 Nil_1)))
(declare-fun epsR_0 (R_0 R_0) Bool)
(assert (forall ((x_16 R_0))
	(=> (eps_1 true_0 x_16)
	    (epsR_0 Eps_0 x_16))))
(assert (forall ((x_2066 Bool_0) (x_16 R_0))
	(=>	(and (diseqBool_0 x_2066 true_0)
			(eps_1 x_2066 x_16))
		(epsR_0 Nil_1 x_16))))
(declare-fun step_0 (R_0 R_0 A_0) Bool)
(assert (forall ((x_2068 R_0) (x_2069 R_0) (p_2 R_0) (y_8 A_0))
	(=>	(and (step_0 x_2069 p_2 y_8)
			(seq_1 x_2068 x_2069 (Star_0 p_2)))
		(step_0 x_2068 (Star_0 p_2) y_8))))
(assert (forall ((x_2071 R_0) (x_2072 R_0) (x_2073 R_0) (x_2074 R_0) (x_2075 R_0) (x_2076 R_0) (r_2 R_0) (q_3 R_0) (y_8 A_0))
	(=>	(and (step_0 x_2072 r_2 y_8)
			(seq_1 x_2073 x_2072 q_3)
			(epsR_0 x_2074 r_2)
			(step_0 x_2075 q_3 y_8)
			(seq_1 x_2076 x_2074 x_2075)
			(plus_1 x_2071 x_2073 x_2076))
		(step_0 x_2071 (Seq_0 r_2 q_3) y_8))))
(assert (forall ((x_2078 R_0) (x_2079 R_0) (x_2080 R_0) (p_1 R_0) (q_2 R_0) (y_8 A_0))
	(=>	(and (step_0 x_2079 p_1 y_8)
			(step_0 x_2080 q_2 y_8)
			(plus_1 x_2078 x_2079 x_2080))
		(step_0 x_2078 (Plus_0 p_1 q_2) y_8))))
(assert (forall ((a_1 A_0) (y_8 A_0))
	(=> (eqA_0 true_0 a_1 y_8)
	    (step_0 Eps_0 (Atom_0 a_1) y_8))))
(assert (forall ((x_2084 Bool_0) (a_1 A_0) (y_8 A_0))
	(=>	(and (diseqBool_0 x_2084 true_0)
			(eqA_0 x_2084 a_1 y_8))
		(step_0 Nil_1 (Atom_0 a_1) y_8))))
(assert (forall ((x_18 R_0) (y_8 A_0))
	(step_0 Nil_1 Eps_0 y_8)))
(assert (forall ((x_18 R_0) (y_8 A_0))
	(step_0 Nil_1 Nil_1 y_8)))
(declare-fun recognise_0 (Bool_0 R_0 list_1) Bool)
(assert (forall ((x_2088 Bool_0) (x_2089 R_0) (z_1 A_0) (xs_2 list_1) (x_19 R_0))
	(=>	(and (step_0 x_2089 x_19 z_1)
			(recognise_0 x_2088 x_2089 xs_2))
		(recognise_0 x_2088 x_19 (cons_1 z_1 xs_2)))))
(assert (forall ((x_2091 Bool_0) (x_19 R_0))
	(=> (eps_1 x_2091 x_19)
	    (recognise_0 x_2091 x_19 nil_2))))
(declare-fun formula_0 (list_0 R_0 R_0 list_2) Bool)
(assert (forall ((x_2105 Bool_0) (x_2094 Bool_0) (x_2095 Bool_0) (x_2096 list_0) (s_1 list_1) (s_2 list_1) (z_2 list_2) (p_3 R_0) (q_4 R_0))
	(=>	(and (recognise_0 x_2094 p_3 s_1)
			(recognise_0 x_2095 q_4 s_2)
			(formula_0 x_2096 p_3 q_4 z_2)
			(and_0 x_2105 x_2094 x_2095))
		(formula_0 (cons_0 x_2105 x_2096) p_3 q_4 (cons_2 (pair_1 s_1 s_2) z_2)))))
(assert (forall ((p_3 R_0) (q_4 R_0))
	(formula_0 nil_0 p_3 q_4 nil_3)))
(assert (forall ((x_2098 Bool_0) (x_2099 list_2) (x_2100 list_0) (x_2101 Bool_0) (p_4 R_0) (q_5 R_0) (s_3 list_1))
	(=>	(and (diseqBool_0 x_2098 x_2101)
			(recognise_0 x_2098 (Seq_0 p_4 q_5) s_3)
			(split_1 x_2099 s_3)
			(formula_0 x_2100 p_4 q_5 x_2099)
			(or_0 x_2101 x_2100))
		false)))
(check-sat)
