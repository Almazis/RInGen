(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_14 ) (Z_15 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_261 Nat_0))
	(unS_1 x_261 (Z_15 x_261))))
(assert (isZ_2 Z_14))
(assert (forall ((x_263 Nat_0))
	(isZ_3 (Z_15 x_263))))
(assert (forall ((x_264 Nat_0))
	(diseqNat_0 Z_14 (Z_15 x_264))))
(assert (forall ((x_265 Nat_0))
	(diseqNat_0 (Z_15 x_265) Z_14)))
(assert (forall ((x_266 Nat_0) (x_267 Nat_0))
	(=> (diseqNat_0 x_266 x_267)
	    (diseqNat_0 (Z_15 x_266) (Z_15 x_267)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_20 Nat_0))
	(add_0 y_20 Z_14 y_20)))
(assert (forall ((r_0 Nat_0) (x_202 Nat_0) (y_20 Nat_0))
	(=> (add_0 r_0 x_202 y_20)
	    (add_0 (Z_15 r_0) (Z_15 x_202) y_20))))
(assert (forall ((y_20 Nat_0))
	(minus_0 Z_14 Z_14 y_20)))
(assert (forall ((r_0 Nat_0) (x_202 Nat_0) (y_20 Nat_0))
	(=> (minus_0 r_0 x_202 y_20)
	    (minus_0 (Z_15 r_0) (Z_15 x_202) y_20))))
(assert (forall ((y_20 Nat_0))
	(le_0 Z_14 y_20)))
(assert (forall ((x_202 Nat_0) (y_20 Nat_0))
	(=> (le_0 x_202 y_20)
	    (le_0 (Z_15 x_202) (Z_15 y_20)))))
(assert (forall ((y_20 Nat_0))
	(ge_0 y_20 Z_14)))
(assert (forall ((x_202 Nat_0) (y_20 Nat_0))
	(=> (ge_0 x_202 y_20)
	    (ge_0 (Z_15 x_202) (Z_15 y_20)))))
(assert (forall ((y_20 Nat_0))
	(lt_0 Z_14 (Z_15 y_20))))
(assert (forall ((x_202 Nat_0) (y_20 Nat_0))
	(=> (lt_0 x_202 y_20)
	    (lt_0 (Z_15 x_202) (Z_15 y_20)))))
(assert (forall ((y_20 Nat_0))
	(gt_0 (Z_15 y_20) Z_14)))
(assert (forall ((x_202 Nat_0) (y_20 Nat_0))
	(=> (gt_0 x_202 y_20)
	    (gt_0 (Z_15 x_202) (Z_15 y_20)))))
(assert (forall ((y_20 Nat_0))
	(mult_0 Z_14 Z_14 y_20)))
(assert (forall ((r_0 Nat_0) (x_202 Nat_0) (y_20 Nat_0) (z_16 Nat_0))
	(=>	(and (mult_0 r_0 x_202 y_20)
			(add_0 z_16 r_0 y_20))
		(mult_0 z_16 (Z_15 x_202) y_20))))
(assert (forall ((x_202 Nat_0) (y_20 Nat_0))
	(=> (lt_0 x_202 y_20)
	    (div_0 Z_14 x_202 y_20))))
(assert (forall ((r_0 Nat_0) (x_202 Nat_0) (y_20 Nat_0) (z_16 Nat_0))
	(=>	(and (ge_0 x_202 y_20)
			(minus_0 z_16 x_202 y_20)
			(div_0 r_0 z_16 y_20))
		(div_0 (Z_15 r_0) x_202 y_20))))
(assert (forall ((x_202 Nat_0) (y_20 Nat_0))
	(=> (lt_0 x_202 y_20)
	    (mod_0 x_202 x_202 y_20))))
(assert (forall ((r_0 Nat_0) (x_202 Nat_0) (y_20 Nat_0) (z_16 Nat_0))
	(=>	(and (ge_0 x_202 y_20)
			(minus_0 z_16 x_202 y_20)
			(mod_0 r_0 z_16 y_20))
		(mod_0 r_0 x_202 y_20))))
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
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_0) (projpair_1 Nat_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (Nat_0 pair_0) Bool)
(declare-fun projpair_3 (Nat_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_270 Nat_0) (x_271 Nat_0))
	(projpair_2 x_270 (pair_1 x_270 x_271))))
(assert (forall ((x_270 Nat_0) (x_271 Nat_0))
	(projpair_3 x_271 (pair_1 x_270 x_271))))
(assert (forall ((x_273 Nat_0) (x_274 Nat_0))
	(ispair_0 (pair_1 x_273 x_274))))
(assert (forall ((x_275 Nat_0) (x_276 Nat_0) (x_277 Nat_0) (x_278 Nat_0))
	(=> (diseqNat_0 x_275 x_277)
	    (diseqpair_0 (pair_1 x_275 x_276) (pair_1 x_277 x_278)))))
(assert (forall ((x_275 Nat_0) (x_276 Nat_0) (x_277 Nat_0) (x_278 Nat_0))
	(=> (diseqNat_0 x_276 x_278)
	    (diseqpair_0 (pair_1 x_275 x_276) (pair_1 x_277 x_278)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Bool_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_3 (Bool_0 list_0) Bool)
(declare-fun tail_3 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_280 Bool_0) (x_281 list_0))
	(head_3 x_280 (cons_0 x_280 x_281))))
(assert (forall ((x_280 Bool_0) (x_281 list_0))
	(tail_3 x_281 (cons_0 x_280 x_281))))
(assert (isnil_0 nil_0))
(assert (forall ((x_283 Bool_0) (x_284 list_0))
	(iscons_0 (cons_0 x_283 x_284))))
(assert (forall ((x_285 Bool_0) (x_286 list_0))
	(diseqlist_0 nil_0 (cons_0 x_285 x_286))))
(assert (forall ((x_287 Bool_0) (x_288 list_0))
	(diseqlist_0 (cons_0 x_287 x_288) nil_0)))
(assert (forall ((x_289 Bool_0) (x_290 list_0) (x_291 Bool_0) (x_292 list_0))
	(=> (diseqBool_0 x_289 x_291)
	    (diseqlist_0 (cons_0 x_289 x_290) (cons_0 x_291 x_292)))))
(assert (forall ((x_289 Bool_0) (x_290 list_0) (x_291 Bool_0) (x_292 list_0))
	(=> (diseqlist_0 x_290 x_292)
	    (diseqlist_0 (cons_0 x_289 x_290) (cons_0 x_291 x_292)))))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 Nat_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_4 (Nat_0 list_1) Bool)
(declare-fun tail_4 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_294 Nat_0) (x_295 list_1))
	(head_4 x_294 (cons_1 x_294 x_295))))
(assert (forall ((x_294 Nat_0) (x_295 list_1))
	(tail_4 x_295 (cons_1 x_294 x_295))))
(assert (isnil_1 nil_1))
(assert (forall ((x_297 Nat_0) (x_298 list_1))
	(iscons_1 (cons_1 x_297 x_298))))
(assert (forall ((x_299 Nat_0) (x_300 list_1))
	(diseqlist_1 nil_1 (cons_1 x_299 x_300))))
(assert (forall ((x_301 Nat_0) (x_302 list_1))
	(diseqlist_1 (cons_1 x_301 x_302) nil_1)))
(assert (forall ((x_303 Nat_0) (x_304 list_1) (x_305 Nat_0) (x_306 list_1))
	(=> (diseqNat_0 x_303 x_305)
	    (diseqlist_1 (cons_1 x_303 x_304) (cons_1 x_305 x_306)))))
(assert (forall ((x_303 Nat_0) (x_304 list_1) (x_305 Nat_0) (x_306 list_1))
	(=> (diseqlist_1 x_304 x_306)
	    (diseqlist_1 (cons_1 x_303 x_304) (cons_1 x_305 x_306)))))
(declare-datatypes ((list_2 0)) (((nil_2 ) (cons_2 (head_2 pair_0) (tail_2 list_2)))))
(declare-fun diseqlist_2 (list_2 list_2) Bool)
(declare-fun head_5 (pair_0 list_2) Bool)
(declare-fun tail_5 (list_2 list_2) Bool)
(declare-fun isnil_2 (list_2) Bool)
(declare-fun iscons_2 (list_2) Bool)
(assert (forall ((x_308 pair_0) (x_309 list_2))
	(head_5 x_308 (cons_2 x_308 x_309))))
(assert (forall ((x_308 pair_0) (x_309 list_2))
	(tail_5 x_309 (cons_2 x_308 x_309))))
(assert (isnil_2 nil_2))
(assert (forall ((x_311 pair_0) (x_312 list_2))
	(iscons_2 (cons_2 x_311 x_312))))
(assert (forall ((x_313 pair_0) (x_314 list_2))
	(diseqlist_2 nil_2 (cons_2 x_313 x_314))))
(assert (forall ((x_315 pair_0) (x_316 list_2))
	(diseqlist_2 (cons_2 x_315 x_316) nil_2)))
(assert (forall ((x_317 pair_0) (x_318 list_2) (x_319 pair_0) (x_320 list_2))
	(=> (diseqpair_0 x_317 x_319)
	    (diseqlist_2 (cons_2 x_317 x_318) (cons_2 x_319 x_320)))))
(assert (forall ((x_317 pair_0) (x_318 list_2) (x_319 pair_0) (x_320 list_2))
	(=> (diseqlist_2 x_318 x_320)
	    (diseqlist_2 (cons_2 x_317 x_318) (cons_2 x_319 x_320)))))
(declare-fun primEnumFromTo_0 (list_1 Nat_0 Nat_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 Nat_0))
	(=> (gt_0 x_0 y_0)
	    (primEnumFromTo_0 nil_1 x_0 y_0))))
(assert (forall ((x_203 Nat_0) (x_33 list_1) (x_0 Nat_0) (y_0 Nat_0))
	(=>	(and (le_0 x_0 y_0)
			(primEnumFromTo_0 x_33 x_203 y_0)
			(add_0 x_203 (Z_15 Z_14) x_0))
		(primEnumFromTo_0 (cons_1 x_0 x_33) x_0 y_0))))
(declare-fun path_0 (list_0 Nat_0 Nat_0 list_2) Bool)
(assert (forall ((x_35 list_0) (u_0 Nat_0) (x_3 list_2))
	(=> (path_0 x_35 u_0 u_0 x_3)
	    (path_0 (cons_0 true_0 x_35) u_0 u_0 (cons_2 (pair_1 u_0 u_0) x_3)))))
(assert (forall ((x_37 list_0) (u_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 u_0 u_0)
			(path_0 x_37 u_0 u_0 x_3))
		(path_0 (cons_0 true_0 x_37) u_0 u_0 (cons_2 (pair_1 u_0 u_0) x_3)))))
(assert (forall ((x_39 list_0) (u_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 u_0 u_0)
			(path_0 x_39 u_0 u_0 x_3))
		(path_0 (cons_0 true_0 x_39) u_0 u_0 (cons_2 (pair_1 u_0 u_0) x_3)))))
(assert (forall ((x_41 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 u_0 v_0)
			(diseqNat_0 v_0 u_0)
			(path_0 x_41 v_0 u_0 x_3))
		(path_0 (cons_0 true_0 x_41) v_0 u_0 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_43 list_0) (u_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 u_0 u_0)
			(path_0 x_43 u_0 u_0 x_3))
		(path_0 (cons_0 true_0 x_43) u_0 u_0 (cons_2 (pair_1 u_0 u_0) x_3)))))
(assert (forall ((x_45 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 u_0 v_0)
			(diseqNat_0 u_0 v_0)
			(path_0 x_45 v_0 v_0 x_3))
		(path_0 (cons_0 false_0 x_45) v_0 v_0 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_47 list_0) (u_0 Nat_0) (x_3 list_2) (y_1 Nat_0))
	(=>	(and (diseqNat_0 u_0 y_1)
			(diseqNat_0 u_0 y_1)
			(path_0 x_47 u_0 y_1 x_3))
		(path_0 (cons_0 false_0 x_47) u_0 y_1 (cons_2 (pair_1 u_0 u_0) x_3)))))
(assert (forall ((x_49 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2) (y_1 Nat_0))
	(=>	(and (diseqNat_0 u_0 v_0)
			(diseqNat_0 v_0 y_1)
			(diseqNat_0 u_0 y_1)
			(path_0 x_49 v_0 y_1 x_3))
		(path_0 (cons_0 false_0 x_49) v_0 y_1 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_51 list_0) (u_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 u_0 u_0)
			(path_0 x_51 u_0 u_0 x_3))
		(path_0 (cons_0 true_0 x_51) u_0 u_0 (cons_2 (pair_1 u_0 u_0) x_3)))))
(assert (forall ((x_53 list_0) (u_0 Nat_0) (x_3 list_2) (x_1 Nat_0))
	(=>	(and (diseqNat_0 u_0 x_1)
			(diseqNat_0 u_0 x_1)
			(path_0 x_53 x_1 u_0 x_3))
		(path_0 (cons_0 false_0 x_53) x_1 u_0 (cons_2 (pair_1 u_0 u_0) x_3)))))
(assert (forall ((x_55 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 v_0 u_0)
			(diseqNat_0 v_0 u_0)
			(path_0 x_55 u_0 u_0 x_3))
		(path_0 (cons_0 false_0 x_55) u_0 u_0 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_57 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2) (x_1 Nat_0))
	(=>	(and (diseqNat_0 u_0 x_1)
			(diseqNat_0 v_0 u_0)
			(diseqNat_0 v_0 x_1)
			(path_0 x_57 x_1 u_0 x_3))
		(path_0 (cons_0 false_0 x_57) x_1 u_0 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_59 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2))
	(=>	(and (diseqNat_0 u_0 v_0)
			(diseqNat_0 v_0 u_0)
			(path_0 x_59 u_0 v_0 x_3))
		(path_0 (cons_0 true_0 x_59) u_0 v_0 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_61 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2) (x_1 Nat_0))
	(=>	(and (diseqNat_0 u_0 x_1)
			(diseqNat_0 u_0 v_0)
			(diseqNat_0 v_0 x_1)
			(path_0 x_61 x_1 v_0 x_3))
		(path_0 (cons_0 false_0 x_61) x_1 v_0 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_63 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2) (y_1 Nat_0))
	(=>	(and (diseqNat_0 v_0 y_1)
			(diseqNat_0 u_0 y_1)
			(diseqNat_0 v_0 u_0)
			(path_0 x_63 u_0 y_1 x_3))
		(path_0 (cons_0 false_0 x_63) u_0 y_1 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_65 list_0) (u_0 Nat_0) (v_0 Nat_0) (x_3 list_2) (x_1 Nat_0) (y_1 Nat_0))
	(=>	(and (diseqNat_0 u_0 x_1)
			(diseqNat_0 v_0 y_1)
			(diseqNat_0 u_0 y_1)
			(diseqNat_0 v_0 x_1)
			(path_0 x_65 x_1 y_1 x_3))
		(path_0 (cons_0 false_0 x_65) x_1 y_1 (cons_2 (pair_1 u_0 v_0) x_3)))))
(assert (forall ((x_1 Nat_0) (y_1 Nat_0))
	(path_0 nil_0 x_1 y_1 nil_2)))
(declare-fun or_0 (Bool_0 list_0) Bool)
(assert (forall ((x_198 Bool_0) (x_68 Bool_0) (y_2 Bool_0) (xs_0 list_0))
	(=>	(and (or_0 x_68 xs_0)
			(or_1 x_198 y_2 x_68))
		(or_0 x_198 (cons_0 y_2 xs_0)))))
(assert (or_0 false_0 nil_0))
(declare-fun path_1 (Bool_0 list_1 list_2) Bool)
(assert (forall ((x_199 Bool_0) (x_71 list_0) (x_72 Bool_0) (x_73 Bool_0) (y_4 Nat_0) (xs_1 list_1) (z_1 Nat_0) (y_3 list_2))
	(=>	(and (path_0 x_71 z_1 y_4 y_3)
			(or_0 x_72 x_71)
			(path_1 x_73 (cons_1 y_4 xs_1) y_3)
			(and_0 x_199 x_72 x_73))
		(path_1 x_199 (cons_1 z_1 (cons_1 y_4 xs_1)) y_3))))
(assert (forall ((z_1 Nat_0) (y_3 list_2))
	(path_1 true_0 (cons_1 z_1 nil_1) y_3)))
(assert (forall ((y_3 list_2))
	(path_1 true_0 nil_1 y_3)))
(declare-fun maximummaximum_0 (Nat_0 Nat_0 list_2) Bool)
(assert (forall ((x_76 Nat_0) (y_7 Nat_0) (y_6 Nat_0) (yzs_0 list_2) (x_7 Nat_0))
	(=>	(and (le_0 y_6 y_7)
			(le_0 x_7 y_7)
			(maximummaximum_0 x_76 y_7 yzs_0))
		(maximummaximum_0 x_76 x_7 (cons_2 (pair_1 y_6 y_7) yzs_0)))))
(assert (forall ((x_78 Nat_0) (y_7 Nat_0) (y_6 Nat_0) (yzs_0 list_2) (x_7 Nat_0))
	(=>	(and (le_0 y_6 y_7)
			(gt_0 x_7 y_7)
			(maximummaximum_0 x_78 x_7 yzs_0))
		(maximummaximum_0 x_78 x_7 (cons_2 (pair_1 y_6 y_7) yzs_0)))))
(assert (forall ((x_80 Nat_0) (y_6 Nat_0) (z_3 Nat_0) (yzs_0 list_2) (x_7 Nat_0))
	(=>	(and (gt_0 y_6 z_3)
			(le_0 x_7 y_6)
			(maximummaximum_0 x_80 y_6 yzs_0))
		(maximummaximum_0 x_80 x_7 (cons_2 (pair_1 y_6 z_3) yzs_0)))))
(assert (forall ((x_82 Nat_0) (y_6 Nat_0) (z_3 Nat_0) (yzs_0 list_2) (x_7 Nat_0))
	(=>	(and (gt_0 y_6 z_3)
			(gt_0 x_7 y_6)
			(maximummaximum_0 x_82 x_7 yzs_0))
		(maximummaximum_0 x_82 x_7 (cons_2 (pair_1 y_6 z_3) yzs_0)))))
(assert (forall ((x_7 Nat_0))
	(maximummaximum_0 x_7 x_7 nil_2)))
(declare-fun length_0 (Nat_0 list_1) Bool)
(assert (forall ((x_204 Nat_0) (x_86 Nat_0) (y_8 Nat_0) (l_0 list_1))
	(=>	(and (length_0 x_86 l_0)
			(add_0 x_204 (Z_15 Z_14) x_86))
		(length_0 x_204 (cons_1 y_8 l_0)))))
(assert (length_0 Z_14 nil_1))
(declare-fun last_0 (Nat_0 Nat_0 list_1) Bool)
(assert (forall ((x_88 Nat_0) (z_4 Nat_0) (ys_0 list_1) (x_9 Nat_0))
	(=> (last_0 x_88 z_4 ys_0)
	    (last_0 x_88 x_9 (cons_1 z_4 ys_0)))))
(assert (forall ((x_9 Nat_0))
	(last_0 x_9 x_9 nil_1)))
(declare-fun elem_0 (Bool_0 Nat_0 list_1) Bool)
(assert (forall ((xs_2 list_1) (x_10 Nat_0))
	(elem_0 true_0 x_10 (cons_1 x_10 xs_2))))
(assert (forall ((x_92 Bool_0) (z_5 Nat_0) (xs_2 list_1) (x_10 Nat_0))
	(=>	(and (diseqNat_0 z_5 x_10)
			(elem_0 x_92 x_10 xs_2))
		(elem_0 x_92 x_10 (cons_1 z_5 xs_2)))))
(assert (forall ((x_10 Nat_0))
	(elem_0 false_0 x_10 nil_1)))
(declare-fun unique_0 (Bool_0 list_1) Bool)
(assert (forall ((y_11 Nat_0) (xs_3 list_1))
	(=> (elem_0 true_0 y_11 xs_3)
	    (unique_0 false_0 (cons_1 y_11 xs_3)))))
(assert (forall ((x_98 Bool_0) (x_97 Bool_0) (y_11 Nat_0) (xs_3 list_1))
	(=>	(and (diseqBool_0 x_97 true_0)
			(unique_0 x_98 xs_3)
			(elem_0 x_97 y_11 xs_3))
		(unique_0 x_98 (cons_1 y_11 xs_3)))))
(assert (unique_0 true_0 nil_1))
(declare-fun tour_0 (Bool_0 list_1 list_2) Bool)
(assert (forall ((x_104 Bool_0) (x_105 Bool_0) (x_106 Bool_0) (x_102 Nat_0) (x_103 Nat_0) (x_101 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_15 list_1))
	(=>	(and (le_0 u_1 v_1)
			(path_1 x_105 (cons_1 x_101 x_15) (cons_2 (pair_1 u_1 v_1) vs_0))
			(unique_0 x_106 x_15)
			(length_0 x_102 (cons_1 x_101 x_15))
			(maximummaximum_0 x_103 v_1 vs_0)
			(last_0 x_101 x_101 x_15)
			(and_0 x_104 x_105 x_106)
			(add_0 x_102 (Z_15 (Z_15 Z_14)) x_103))
		(tour_0 x_104 (cons_1 x_101 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_108 Nat_0) (x_109 Nat_0) (x_107 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_14 Nat_0) (x_15 list_1))
	(=>	(and (diseqNat_0 x_14 x_107)
			(le_0 u_1 v_1)
			(length_0 x_108 (cons_1 x_14 x_15))
			(maximummaximum_0 x_109 v_1 vs_0)
			(last_0 x_107 x_14 x_15)
			(add_0 x_108 (Z_15 (Z_15 Z_14)) x_109))
		(tour_0 false_0 (cons_1 x_14 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_207 Nat_0) (x_112 Nat_0) (x_113 Nat_0) (x_111 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_15 list_1))
	(=>	(and (diseqNat_0 x_112 x_207)
			(le_0 u_1 v_1)
			(length_0 x_112 (cons_1 x_111 x_15))
			(maximummaximum_0 x_113 v_1 vs_0)
			(last_0 x_111 x_111 x_15)
			(add_0 x_207 (Z_15 (Z_15 Z_14)) x_113))
		(tour_0 false_0 (cons_1 x_111 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_208 Nat_0) (x_116 Nat_0) (x_117 Nat_0) (x_115 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_14 Nat_0) (x_15 list_1))
	(=>	(and (diseqNat_0 x_14 x_115)
			(diseqNat_0 x_116 x_208)
			(le_0 u_1 v_1)
			(length_0 x_116 (cons_1 x_14 x_15))
			(maximummaximum_0 x_117 v_1 vs_0)
			(last_0 x_115 x_14 x_15)
			(add_0 x_208 (Z_15 (Z_15 Z_14)) x_117))
		(tour_0 false_0 (cons_1 x_14 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_122 Bool_0) (x_123 Bool_0) (x_124 Bool_0) (x_120 Nat_0) (x_121 Nat_0) (x_119 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_15 list_1))
	(=>	(and (gt_0 u_1 v_1)
			(path_1 x_123 (cons_1 x_119 x_15) (cons_2 (pair_1 u_1 v_1) vs_0))
			(unique_0 x_124 x_15)
			(length_0 x_120 (cons_1 x_119 x_15))
			(maximummaximum_0 x_121 u_1 vs_0)
			(last_0 x_119 x_119 x_15)
			(and_0 x_122 x_123 x_124)
			(add_0 x_120 (Z_15 (Z_15 Z_14)) x_121))
		(tour_0 x_122 (cons_1 x_119 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_126 Nat_0) (x_127 Nat_0) (x_125 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_14 Nat_0) (x_15 list_1))
	(=>	(and (diseqNat_0 x_14 x_125)
			(gt_0 u_1 v_1)
			(length_0 x_126 (cons_1 x_14 x_15))
			(maximummaximum_0 x_127 u_1 vs_0)
			(last_0 x_125 x_14 x_15)
			(add_0 x_126 (Z_15 (Z_15 Z_14)) x_127))
		(tour_0 false_0 (cons_1 x_14 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_211 Nat_0) (x_130 Nat_0) (x_131 Nat_0) (x_129 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_15 list_1))
	(=>	(and (diseqNat_0 x_130 x_211)
			(gt_0 u_1 v_1)
			(length_0 x_130 (cons_1 x_129 x_15))
			(maximummaximum_0 x_131 u_1 vs_0)
			(last_0 x_129 x_129 x_15)
			(add_0 x_211 (Z_15 (Z_15 Z_14)) x_131))
		(tour_0 false_0 (cons_1 x_129 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_212 Nat_0) (x_134 Nat_0) (x_135 Nat_0) (x_133 Nat_0) (u_1 Nat_0) (v_1 Nat_0) (vs_0 list_2) (x_14 Nat_0) (x_15 list_1))
	(=>	(and (diseqNat_0 x_14 x_133)
			(diseqNat_0 x_134 x_212)
			(gt_0 u_1 v_1)
			(length_0 x_134 (cons_1 x_14 x_15))
			(maximummaximum_0 x_135 u_1 vs_0)
			(last_0 x_133 x_14 x_15)
			(add_0 x_212 (Z_15 (Z_15 Z_14)) x_135))
		(tour_0 false_0 (cons_1 x_14 x_15) (cons_2 (pair_1 u_1 v_1) vs_0)))))
(assert (forall ((x_14 Nat_0) (x_15 list_1))
	(tour_0 false_0 (cons_1 x_14 x_15) nil_2)))
(assert (forall ((z_6 pair_0) (x_13 list_2))
	(tour_0 false_0 nil_1 (cons_2 z_6 x_13))))
(assert (tour_0 true_0 nil_1 nil_2))
(declare-fun dodeca_0 (list_2 Nat_0 list_1) Bool)
(assert (forall ((x_213 Nat_0) (x_214 Nat_0) (x_215 Nat_0) (x_216 Nat_0) (x_217 Nat_0) (x_218 Nat_0) (x_219 Nat_0) (x_141 list_2) (z_7 Nat_0) (x_18 list_1) (x_17 Nat_0))
	(=>	(and (dodeca_0 x_141 x_17 x_18)
			(add_0 x_213 x_17 x_17)
			(add_0 x_214 x_213 x_17)
			(add_0 x_215 x_214 z_7)
			(add_0 x_216 x_17 x_17)
			(add_0 x_217 x_216 x_17)
			(add_0 x_218 (Z_15 Z_14) z_7)
			(add_0 x_219 x_217 x_218))
		(dodeca_0 (cons_2 (pair_1 x_215 x_219) x_141) x_17 (cons_1 z_7 x_18)))))
(assert (forall ((x_17 Nat_0))
	(dodeca_0 nil_2 x_17 nil_1)))
(declare-fun dodeca_1 (list_2 Nat_0 list_1) Bool)
(assert (forall ((x_220 Nat_0) (x_221 Nat_0) (x_222 Nat_0) (x_223 Nat_0) (x_224 Nat_0) (x_144 list_2) (z_8 Nat_0) (x_20 list_1) (x_19 Nat_0))
	(=>	(and (dodeca_1 x_144 x_19 x_20)
			(add_0 x_220 x_19 x_19)
			(add_0 x_221 x_220 z_8)
			(add_0 x_222 x_19 x_19)
			(add_0 x_223 x_222 x_19)
			(add_0 x_224 x_223 z_8))
		(dodeca_1 (cons_2 (pair_1 x_221 x_224) x_144) x_19 (cons_1 z_8 x_20)))))
(assert (forall ((x_19 Nat_0))
	(dodeca_1 nil_2 x_19 nil_1)))
(declare-fun dodeca_2 (list_2 Nat_0 list_1) Bool)
(assert (forall ((x_225 Nat_0) (x_226 Nat_0) (x_227 Nat_0) (x_228 Nat_0) (x_147 list_2) (z_9 Nat_0) (x_22 list_1) (x_21 Nat_0))
	(=>	(and (dodeca_2 x_147 x_21 x_22)
			(add_0 x_225 (Z_15 Z_14) z_9)
			(add_0 x_226 x_21 x_225)
			(add_0 x_227 x_21 x_21)
			(add_0 x_228 x_227 z_9))
		(dodeca_2 (cons_2 (pair_1 x_226 x_228) x_147) x_21 (cons_1 z_9 x_22)))))
(assert (forall ((x_21 Nat_0))
	(dodeca_2 nil_2 x_21 nil_1)))
(declare-fun dodeca_3 (list_2 Nat_0 list_1) Bool)
(assert (forall ((x_229 Nat_0) (x_230 Nat_0) (x_231 Nat_0) (x_150 list_2) (z_10 Nat_0) (x_24 list_1) (x_23 Nat_0))
	(=>	(and (dodeca_3 x_150 x_23 x_24)
			(add_0 x_229 x_23 z_10)
			(add_0 x_230 x_23 x_23)
			(add_0 x_231 x_230 z_10))
		(dodeca_3 (cons_2 (pair_1 x_229 x_231) x_150) x_23 (cons_1 z_10 x_24)))))
(assert (forall ((x_23 Nat_0))
	(dodeca_3 nil_2 x_23 nil_1)))
(declare-fun dodeca_4 (list_2 Nat_0 list_1) Bool)
(assert (forall ((x_232 Nat_0) (x_153 list_2) (z_11 Nat_0) (x_26 list_1) (x_25 Nat_0))
	(=>	(and (dodeca_4 x_153 x_25 x_26)
			(add_0 x_232 x_25 z_11))
		(dodeca_4 (cons_2 (pair_1 z_11 x_232) x_153) x_25 (cons_1 z_11 x_26)))))
(assert (forall ((x_25 Nat_0))
	(dodeca_4 nil_2 x_25 nil_1)))
(declare-fun dodeca_5 (list_2 list_1) Bool)
(assert (forall ((x_233 Nat_0) (x_156 list_2) (y_18 Nat_0) (z_12 list_1))
	(=>	(and (dodeca_5 x_156 z_12)
			(add_0 x_233 (Z_15 Z_14) y_18))
		(dodeca_5 (cons_2 (pair_1 y_18 x_233) x_156) (cons_1 y_18 z_12)))))
(assert (dodeca_5 nil_2 nil_1))
(declare-fun x_28 (list_2 list_2 list_2) Bool)
(assert (forall ((x_159 list_2) (z_13 pair_0) (xs_4 list_2) (y_19 list_2))
	(=> (x_28 x_159 xs_4 y_19)
	    (x_28 (cons_2 z_13 x_159) (cons_2 z_13 xs_4) y_19))))
(assert (forall ((x_160 list_2))
	(x_28 x_160 nil_2 x_160)))
(declare-fun dodeca_6 (list_2 Nat_0) Bool)
(assert (dodeca_6 nil_2 Z_14))
(assert (forall ((x_246 Nat_0) (x_243 Nat_0) (x_244 Nat_0) (x_245 Nat_0) (x_237 Nat_0) (x_238 Nat_0) (x_239 Nat_0) (x_240 Nat_0) (x_241 Nat_0) (x_242 Nat_0) (x_236 Nat_0) (x_235 Nat_0) (x_234 Nat_0) (x_162 list_2) (x_163 list_1) (x_164 list_2) (x_165 list_1) (x_166 list_2) (x_167 list_1) (x_168 list_2) (x_169 list_1) (x_170 list_2) (x_171 list_1) (x_172 list_2) (x_173 list_1) (x_174 list_2) (x_175 list_2) (x_176 list_2) (x_177 list_2) (x_178 list_2) (x_30 Nat_0))
	(=>	(and (diseqNat_0 x_30 Z_14)
			(primEnumFromTo_0 x_163 Z_14 x_234)
			(dodeca_5 x_164 x_163)
			(primEnumFromTo_0 x_165 Z_14 x_30)
			(dodeca_4 x_166 x_30 x_165)
			(primEnumFromTo_0 x_167 Z_14 x_30)
			(dodeca_3 x_168 x_30 x_167)
			(primEnumFromTo_0 x_169 Z_14 x_235)
			(dodeca_2 x_170 x_30 x_169)
			(primEnumFromTo_0 x_171 Z_14 x_30)
			(dodeca_1 x_172 x_30 x_171)
			(primEnumFromTo_0 x_173 Z_14 x_236)
			(dodeca_0 x_174 x_30 x_173)
			(x_28 x_175 x_172 (cons_2 (pair_1 x_240 x_242) x_174))
			(x_28 x_176 (cons_2 (pair_1 x_30 x_245) x_170) x_175)
			(x_28 x_177 x_168 x_176)
			(x_28 x_178 x_166 x_177)
			(x_28 x_162 (cons_2 (pair_1 x_246 Z_14) x_164) x_178)
			(minus_0 x_246 x_30 (Z_15 Z_14))
			(add_0 x_243 x_30 x_30)
			(minus_0 x_244 x_30 (Z_15 Z_14))
			(add_0 x_245 x_243 x_244)
			(add_0 x_237 x_30 x_30)
			(add_0 x_238 x_237 x_30)
			(minus_0 x_239 x_30 (Z_15 Z_14))
			(add_0 x_240 x_238 x_239)
			(add_0 x_241 x_30 x_30)
			(add_0 x_242 x_241 x_30)
			(minus_0 x_236 x_30 (Z_15 Z_14))
			(minus_0 x_235 x_30 (Z_15 Z_14))
			(minus_0 x_234 x_30 (Z_15 Z_14)))
		(dodeca_6 x_162 x_30))))
(assert (forall ((x_259 Nat_0) (x_256 Nat_0) (x_257 Nat_0) (x_258 Nat_0) (x_250 Nat_0) (x_251 Nat_0) (x_252 Nat_0) (x_253 Nat_0) (x_254 Nat_0) (x_255 Nat_0) (x_249 Nat_0) (x_248 Nat_0) (x_247 Nat_0) (x_180 list_1) (x_181 list_2) (x_182 list_1) (x_183 list_2) (x_184 list_1) (x_185 list_2) (x_186 list_1) (x_187 list_2) (x_188 list_1) (x_189 list_2) (x_190 list_1) (x_191 list_2) (x_192 list_2) (x_193 list_2) (x_194 list_2) (x_195 list_2) (x_196 list_2) (p_0 list_1))
	(=>	(and (primEnumFromTo_0 x_180 Z_14 x_247)
			(dodeca_5 x_181 x_180)
			(primEnumFromTo_0 x_182 Z_14 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(dodeca_4 x_183 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) x_182)
			(primEnumFromTo_0 x_184 Z_14 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(dodeca_3 x_185 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) x_184)
			(primEnumFromTo_0 x_186 Z_14 x_248)
			(dodeca_2 x_187 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) x_186)
			(primEnumFromTo_0 x_188 Z_14 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(dodeca_1 x_189 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) x_188)
			(primEnumFromTo_0 x_190 Z_14 x_249)
			(dodeca_0 x_191 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) x_190)
			(x_28 x_192 x_189 (cons_2 (pair_1 x_253 x_255) x_191))
			(x_28 x_193 (cons_2 (pair_1 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) x_258) x_187) x_192)
			(x_28 x_194 x_185 x_193)
			(x_28 x_195 x_183 x_194)
			(x_28 x_196 (cons_2 (pair_1 x_259 Z_14) x_181) x_195)
			(tour_0 true_0 p_0 x_196)
			(minus_0 x_259 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 Z_14))
			(add_0 x_256 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(minus_0 x_257 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 Z_14))
			(add_0 x_258 x_256 x_257)
			(add_0 x_250 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(add_0 x_251 x_250 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(minus_0 x_252 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 Z_14))
			(add_0 x_253 x_251 x_252)
			(add_0 x_254 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(add_0 x_255 x_254 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))))
			(minus_0 x_249 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 Z_14))
			(minus_0 x_248 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 Z_14))
			(minus_0 x_247 (Z_15 (Z_15 (Z_15 (Z_15 (Z_15 Z_14))))) (Z_15 Z_14)))
		false)))
(check-sat)
