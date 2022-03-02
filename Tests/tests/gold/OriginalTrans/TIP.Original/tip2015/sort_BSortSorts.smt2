(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_6 ) (Z_7 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_88 Nat_0))
	(unS_1 x_88 (Z_7 x_88))))
(assert (isZ_2 Z_6))
(assert (forall ((x_90 Nat_0))
	(isZ_3 (Z_7 x_90))))
(assert (forall ((x_91 Nat_0))
	(diseqNat_0 Z_6 (Z_7 x_91))))
(assert (forall ((x_92 Nat_0))
	(diseqNat_0 (Z_7 x_92) Z_6)))
(assert (forall ((x_93 Nat_0) (x_94 Nat_0))
	(=> (diseqNat_0 x_93 x_94)
	    (diseqNat_0 (Z_7 x_93) (Z_7 x_94)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_10 Nat_0))
	(add_0 y_10 Z_6 y_10)))
(assert (forall ((r_0 Nat_0) (x_86 Nat_0) (y_10 Nat_0))
	(=> (add_0 r_0 x_86 y_10)
	    (add_0 (Z_7 r_0) (Z_7 x_86) y_10))))
(assert (forall ((y_10 Nat_0))
	(minus_0 Z_6 Z_6 y_10)))
(assert (forall ((r_0 Nat_0) (x_86 Nat_0) (y_10 Nat_0))
	(=> (minus_0 r_0 x_86 y_10)
	    (minus_0 (Z_7 r_0) (Z_7 x_86) y_10))))
(assert (forall ((y_10 Nat_0))
	(le_0 Z_6 y_10)))
(assert (forall ((x_86 Nat_0) (y_10 Nat_0))
	(=> (le_0 x_86 y_10)
	    (le_0 (Z_7 x_86) (Z_7 y_10)))))
(assert (forall ((y_10 Nat_0))
	(ge_0 y_10 Z_6)))
(assert (forall ((x_86 Nat_0) (y_10 Nat_0))
	(=> (ge_0 x_86 y_10)
	    (ge_0 (Z_7 x_86) (Z_7 y_10)))))
(assert (forall ((y_10 Nat_0))
	(lt_0 Z_6 (Z_7 y_10))))
(assert (forall ((x_86 Nat_0) (y_10 Nat_0))
	(=> (lt_0 x_86 y_10)
	    (lt_0 (Z_7 x_86) (Z_7 y_10)))))
(assert (forall ((y_10 Nat_0))
	(gt_0 (Z_7 y_10) Z_6)))
(assert (forall ((x_86 Nat_0) (y_10 Nat_0))
	(=> (gt_0 x_86 y_10)
	    (gt_0 (Z_7 x_86) (Z_7 y_10)))))
(assert (forall ((y_10 Nat_0))
	(mult_0 Z_6 Z_6 y_10)))
(assert (forall ((r_0 Nat_0) (x_86 Nat_0) (y_10 Nat_0) (z_8 Nat_0))
	(=>	(and (mult_0 r_0 x_86 y_10)
			(add_0 z_8 r_0 y_10))
		(mult_0 z_8 (Z_7 x_86) y_10))))
(assert (forall ((x_86 Nat_0) (y_10 Nat_0))
	(=> (lt_0 x_86 y_10)
	    (div_0 Z_6 x_86 y_10))))
(assert (forall ((r_0 Nat_0) (x_86 Nat_0) (y_10 Nat_0) (z_8 Nat_0))
	(=>	(and (ge_0 x_86 y_10)
			(minus_0 z_8 x_86 y_10)
			(div_0 r_0 z_8 y_10))
		(div_0 (Z_7 r_0) x_86 y_10))))
(assert (forall ((x_86 Nat_0) (y_10 Nat_0))
	(=> (lt_0 x_86 y_10)
	    (mod_0 x_86 x_86 y_10))))
(assert (forall ((r_0 Nat_0) (x_86 Nat_0) (y_10 Nat_0) (z_8 Nat_0))
	(=>	(and (ge_0 x_86 y_10)
			(minus_0 z_8 x_86 y_10)
			(mod_0 r_0 z_8 y_10))
		(mod_0 r_0 x_86 y_10))))
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
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_98 Nat_0) (x_99 list_0))
	(head_1 x_98 (cons_0 x_98 x_99))))
(assert (forall ((x_98 Nat_0) (x_99 list_0))
	(tail_1 x_99 (cons_0 x_98 x_99))))
(assert (isnil_0 nil_0))
(assert (forall ((x_101 Nat_0) (x_102 list_0))
	(iscons_0 (cons_0 x_101 x_102))))
(assert (forall ((x_103 Nat_0) (x_104 list_0))
	(diseqlist_0 nil_0 (cons_0 x_103 x_104))))
(assert (forall ((x_105 Nat_0) (x_106 list_0))
	(diseqlist_0 (cons_0 x_105 x_106) nil_0)))
(assert (forall ((x_107 Nat_0) (x_108 list_0) (x_109 Nat_0) (x_110 list_0))
	(=> (diseqNat_0 x_107 x_109)
	    (diseqlist_0 (cons_0 x_107 x_108) (cons_0 x_109 x_110)))))
(assert (forall ((x_107 Nat_0) (x_108 list_0) (x_109 Nat_0) (x_110 list_0))
	(=> (diseqlist_0 x_108 x_110)
	    (diseqlist_0 (cons_0 x_107 x_108) (cons_0 x_109 x_110)))))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 Nat_0))
	(=> (le_0 x_0 y_0)
	    (sort_0 (cons_0 x_0 (cons_0 y_0 nil_0)) x_0 y_0))))
(assert (forall ((x_0 Nat_0) (y_0 Nat_0))
	(=> (gt_0 x_0 y_0)
	    (sort_0 (cons_0 y_0 (cons_0 x_0 nil_0)) x_0 y_0))))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_26 Bool_0) (y_2 Nat_0) (xs_0 list_0) (y_1 Nat_0))
	(=>	(and (le_0 y_1 y_2)
			(ordered_0 x_26 (cons_0 y_2 xs_0)))
		(ordered_0 x_26 (cons_0 y_1 (cons_0 y_2 xs_0))))))
(assert (forall ((y_2 Nat_0) (xs_0 list_0) (y_1 Nat_0))
	(=> (gt_0 y_1 y_2)
	    (ordered_0 false_0 (cons_0 y_1 (cons_0 y_2 xs_0))))))
(assert (forall ((y_1 Nat_0))
	(ordered_0 true_0 (cons_0 y_1 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun evens_0 (list_0 list_0) Bool)
(declare-fun odds_0 (list_0 list_0) Bool)
(assert (forall ((x_32 list_0) (y_3 Nat_0) (xs_1 list_0))
	(=> (odds_0 x_32 xs_1)
	    (evens_0 (cons_0 y_3 x_32) (cons_0 y_3 xs_1)))))
(assert (evens_0 nil_0 nil_0))
(assert (forall ((x_34 list_0) (y_4 Nat_0) (xs_2 list_0))
	(=> (evens_0 x_34 xs_2)
	    (odds_0 x_34 (cons_0 y_4 xs_2)))))
(assert (odds_0 nil_0 nil_0))
(declare-fun x_6 (list_0 list_0 list_0) Bool)
(assert (forall ((x_38 list_0) (z_1 Nat_0) (xs_3 list_0) (y_5 list_0))
	(=> (x_6 x_38 xs_3 y_5)
	    (x_6 (cons_0 z_1 x_38) (cons_0 z_1 xs_3) y_5))))
(assert (forall ((x_39 list_0))
	(x_6 x_39 nil_0 x_39)))
(declare-fun pairs_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_40 list_0) (x_41 list_0) (x_42 list_0) (x_10 Nat_0) (x_11 list_0) (z_2 Nat_0) (x_9 list_0))
	(=>	(and (sort_0 x_41 z_2 x_10)
			(pairs_0 x_42 x_9 x_11)
			(x_6 x_40 x_41 x_42))
		(pairs_0 x_40 (cons_0 z_2 x_9) (cons_0 x_10 x_11)))))
(assert (forall ((z_2 Nat_0) (x_9 list_0))
	(pairs_0 (cons_0 z_2 x_9) (cons_0 z_2 x_9) nil_0)))
(assert (forall ((x_45 list_0))
	(pairs_0 x_45 nil_0 x_45)))
(declare-fun stitch_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_47 list_0) (z_3 Nat_0) (xs_4 list_0) (y_7 list_0))
	(=> (pairs_0 x_47 xs_4 y_7)
	    (stitch_0 (cons_0 z_3 x_47) (cons_0 z_3 xs_4) y_7))))
(assert (forall ((x_48 list_0))
	(stitch_0 x_48 nil_0 x_48)))
(declare-fun bmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_49 list_0) (x_50 list_0) (x_51 list_0) (x_52 list_0) (x_53 list_0) (x_54 list_0) (x_19 Nat_0) (x_20 list_0) (fail_0 list_0) (x_15 Nat_0) (x_16 list_0) (z_4 Nat_0))
	(=>	(and (evens_0 x_49 (cons_0 z_4 (cons_0 x_19 x_20)))
			(evens_0 x_50 (cons_0 x_15 x_16))
			(bmerge_0 x_51 x_49 x_50)
			(odds_0 x_52 (cons_0 z_4 (cons_0 x_19 x_20)))
			(odds_0 x_53 (cons_0 x_15 x_16))
			(bmerge_0 x_54 x_52 x_53)
			(stitch_0 fail_0 x_51 x_54))
		(bmerge_0 fail_0 (cons_0 z_4 (cons_0 x_19 x_20)) (cons_0 x_15 x_16)))))
(assert (forall ((x_57 list_0) (x_58 list_0) (x_59 list_0) (x_60 list_0) (x_61 list_0) (x_62 list_0) (x_17 Nat_0) (x_18 list_0) (fail_0 list_0) (x_15 Nat_0) (z_4 Nat_0))
	(=>	(and (evens_0 x_57 (cons_0 z_4 nil_0))
			(evens_0 x_58 (cons_0 x_15 (cons_0 x_17 x_18)))
			(bmerge_0 x_59 x_57 x_58)
			(odds_0 x_60 (cons_0 z_4 nil_0))
			(odds_0 x_61 (cons_0 x_15 (cons_0 x_17 x_18)))
			(bmerge_0 x_62 x_60 x_61)
			(stitch_0 fail_0 x_59 x_62))
		(bmerge_0 fail_0 (cons_0 z_4 nil_0) (cons_0 x_15 (cons_0 x_17 x_18))))))
(assert (forall ((x_72 list_0) (x_65 list_0) (x_66 list_0) (x_67 list_0) (x_68 list_0) (x_69 list_0) (x_70 list_0) (fail_0 list_0) (x_15 Nat_0) (z_4 Nat_0))
	(=>	(and (sort_0 x_72 z_4 x_15)
			(evens_0 x_65 (cons_0 z_4 nil_0))
			(evens_0 x_66 (cons_0 x_15 nil_0))
			(bmerge_0 x_67 x_65 x_66)
			(odds_0 x_68 (cons_0 z_4 nil_0))
			(odds_0 x_69 (cons_0 x_15 nil_0))
			(bmerge_0 x_70 x_68 x_69)
			(stitch_0 fail_0 x_67 x_70))
		(bmerge_0 x_72 (cons_0 z_4 nil_0) (cons_0 x_15 nil_0)))))
(assert (forall ((z_4 Nat_0) (x_14 list_0))
	(bmerge_0 (cons_0 z_4 x_14) (cons_0 z_4 x_14) nil_0)))
(assert (forall ((y_8 list_0))
	(bmerge_0 nil_0 nil_0 y_8)))
(declare-fun bsort_0 (list_0 list_0) Bool)
(assert (forall ((x_76 list_0) (x_77 list_0) (x_78 list_0) (x_79 list_0) (x_80 list_0) (x_22 Nat_0) (x_23 list_0) (y_9 Nat_0))
	(=>	(and (evens_0 x_77 (cons_0 y_9 (cons_0 x_22 x_23)))
			(bsort_0 x_78 x_77)
			(odds_0 x_79 (cons_0 y_9 (cons_0 x_22 x_23)))
			(bsort_0 x_80 x_79)
			(bmerge_0 x_76 x_78 x_80))
		(bsort_0 x_76 (cons_0 y_9 (cons_0 x_22 x_23))))))
(assert (forall ((y_9 Nat_0))
	(bsort_0 (cons_0 y_9 nil_0) (cons_0 y_9 nil_0))))
(assert (bsort_0 nil_0 nil_0))
(assert (forall ((x_84 list_0) (x_85 Bool_0) (xs_5 list_0))
	(=>	(and (diseqBool_0 x_85 true_0)
			(bsort_0 x_84 xs_5)
			(ordered_0 x_85 x_84))
		false)))
(check-sat)
