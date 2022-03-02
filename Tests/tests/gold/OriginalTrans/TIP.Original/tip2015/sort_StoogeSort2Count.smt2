(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_5 ) (Z_6 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_75 Nat_0))
	(unS_1 x_75 (Z_6 x_75))))
(assert (isZ_2 Z_5))
(assert (forall ((x_77 Nat_0))
	(isZ_3 (Z_6 x_77))))
(assert (forall ((x_78 Nat_0))
	(diseqNat_0 Z_5 (Z_6 x_78))))
(assert (forall ((x_79 Nat_0))
	(diseqNat_0 (Z_6 x_79) Z_5)))
(assert (forall ((x_80 Nat_0) (x_81 Nat_0))
	(=> (diseqNat_0 x_80 x_81)
	    (diseqNat_0 (Z_6 x_80) (Z_6 x_81)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_9 Nat_0))
	(add_0 y_9 Z_5 y_9)))
(assert (forall ((r_0 Nat_0) (x_65 Nat_0) (y_9 Nat_0))
	(=> (add_0 r_0 x_65 y_9)
	    (add_0 (Z_6 r_0) (Z_6 x_65) y_9))))
(assert (forall ((y_9 Nat_0))
	(minus_0 Z_5 Z_5 y_9)))
(assert (forall ((r_0 Nat_0) (x_65 Nat_0) (y_9 Nat_0))
	(=> (minus_0 r_0 x_65 y_9)
	    (minus_0 (Z_6 r_0) (Z_6 x_65) y_9))))
(assert (forall ((y_9 Nat_0))
	(le_0 Z_5 y_9)))
(assert (forall ((x_65 Nat_0) (y_9 Nat_0))
	(=> (le_0 x_65 y_9)
	    (le_0 (Z_6 x_65) (Z_6 y_9)))))
(assert (forall ((y_9 Nat_0))
	(ge_0 y_9 Z_5)))
(assert (forall ((x_65 Nat_0) (y_9 Nat_0))
	(=> (ge_0 x_65 y_9)
	    (ge_0 (Z_6 x_65) (Z_6 y_9)))))
(assert (forall ((y_9 Nat_0))
	(lt_0 Z_5 (Z_6 y_9))))
(assert (forall ((x_65 Nat_0) (y_9 Nat_0))
	(=> (lt_0 x_65 y_9)
	    (lt_0 (Z_6 x_65) (Z_6 y_9)))))
(assert (forall ((y_9 Nat_0))
	(gt_0 (Z_6 y_9) Z_5)))
(assert (forall ((x_65 Nat_0) (y_9 Nat_0))
	(=> (gt_0 x_65 y_9)
	    (gt_0 (Z_6 x_65) (Z_6 y_9)))))
(assert (forall ((y_9 Nat_0))
	(mult_0 Z_5 Z_5 y_9)))
(assert (forall ((r_0 Nat_0) (x_65 Nat_0) (y_9 Nat_0) (z_7 Nat_0))
	(=>	(and (mult_0 r_0 x_65 y_9)
			(add_0 z_7 r_0 y_9))
		(mult_0 z_7 (Z_6 x_65) y_9))))
(assert (forall ((x_65 Nat_0) (y_9 Nat_0))
	(=> (lt_0 x_65 y_9)
	    (div_0 Z_5 x_65 y_9))))
(assert (forall ((r_0 Nat_0) (x_65 Nat_0) (y_9 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_65 y_9)
			(minus_0 z_7 x_65 y_9)
			(div_0 r_0 z_7 y_9))
		(div_0 (Z_6 r_0) x_65 y_9))))
(assert (forall ((x_65 Nat_0) (y_9 Nat_0))
	(=> (lt_0 x_65 y_9)
	    (mod_0 x_65 x_65 y_9))))
(assert (forall ((r_0 Nat_0) (x_65 Nat_0) (y_9 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_65 y_9)
			(minus_0 z_7 x_65 y_9)
			(mod_0 r_0 z_7 y_9))
		(mod_0 r_0 x_65 y_9))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_83 Nat_0) (x_84 list_0))
	(head_1 x_83 (cons_0 x_83 x_84))))
(assert (forall ((x_83 Nat_0) (x_84 list_0))
	(tail_1 x_84 (cons_0 x_83 x_84))))
(assert (isnil_0 nil_0))
(assert (forall ((x_86 Nat_0) (x_87 list_0))
	(iscons_0 (cons_0 x_86 x_87))))
(assert (forall ((x_88 Nat_0) (x_89 list_0))
	(diseqlist_0 nil_0 (cons_0 x_88 x_89))))
(assert (forall ((x_90 Nat_0) (x_91 list_0))
	(diseqlist_0 (cons_0 x_90 x_91) nil_0)))
(assert (forall ((x_92 Nat_0) (x_93 list_0) (x_94 Nat_0) (x_95 list_0))
	(=> (diseqNat_0 x_92 x_94)
	    (diseqlist_0 (cons_0 x_92 x_93) (cons_0 x_94 x_95)))))
(assert (forall ((x_92 Nat_0) (x_93 list_0) (x_94 Nat_0) (x_95 list_0))
	(=> (diseqlist_0 x_93 x_95)
	    (diseqlist_0 (cons_0 x_92 x_93) (cons_0 x_94 x_95)))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 list_0) (projpair_1 list_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_2 (list_0 pair_0) Bool)
(declare-fun projpair_3 (list_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_96 list_0) (x_97 list_0))
	(projpair_2 x_96 (pair_1 x_96 x_97))))
(assert (forall ((x_96 list_0) (x_97 list_0))
	(projpair_3 x_97 (pair_1 x_96 x_97))))
(assert (forall ((x_100 list_0) (x_99 list_0))
	(ispair_0 (pair_1 x_99 x_100))))
(assert (forall ((x_101 list_0) (x_102 list_0) (x_103 list_0) (x_104 list_0))
	(=> (diseqlist_0 x_101 x_103)
	    (diseqpair_0 (pair_1 x_101 x_102) (pair_1 x_103 x_104)))))
(assert (forall ((x_101 list_0) (x_102 list_0) (x_103 list_0) (x_104 list_0))
	(=> (diseqlist_0 x_102 x_104)
	    (diseqpair_0 (pair_1 x_101 x_102) (pair_1 x_103 x_104)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_66 Nat_0) (x_20 list_0) (z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=>	(and (gt_0 x_0 Z_5)
			(take_0 x_20 x_66 xs_0)
			(minus_0 x_66 x_0 (Z_6 Z_5)))
		(take_0 (cons_0 z_0 x_20) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_0 Nat_0))
	(=> (gt_0 x_0 Z_5)
	    (take_0 nil_0 x_0 nil_0))))
(declare-fun sort_0 (list_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_1 Nat_0) (y_1 Nat_0))
	(=> (le_0 x_1 y_1)
	    (sort_0 (cons_0 x_1 (cons_0 y_1 nil_0)) x_1 y_1))))
(assert (forall ((x_1 Nat_0) (y_1 Nat_0))
	(=> (gt_0 x_1 y_1)
	    (sort_0 (cons_0 y_1 (cons_0 x_1 nil_0)) x_1 y_1))))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_25 Nat_0) (x_26 Nat_0) (y_2 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_26 l_0)
			(add_0 x_25 (Z_6 Z_5) x_26))
		(length_0 x_25 (cons_0 y_2 l_0)))))
(assert (length_0 Z_5 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_28 list_0) (x_3 Nat_0))
	(=> (le_0 x_3 Z_5)
	    (drop_0 x_28 x_3 x_28))))
(assert (forall ((x_68 Nat_0) (x_29 list_0) (z_1 Nat_0) (xs_1 list_0) (x_3 Nat_0))
	(=>	(and (gt_0 x_3 Z_5)
			(drop_0 x_29 x_68 xs_1)
			(minus_0 x_68 x_3 (Z_6 Z_5)))
		(drop_0 x_29 x_3 (cons_0 z_1 xs_1)))))
(assert (forall ((x_31 list_0) (x_3 Nat_0))
	(=> (le_0 x_3 Z_5)
	    (drop_0 x_31 x_3 x_31))))
(assert (forall ((x_3 Nat_0))
	(=> (gt_0 x_3 Z_5)
	    (drop_0 nil_0 x_3 nil_0))))
(declare-fun splitAt_0 (pair_0 Nat_0 list_0) Bool)
(assert (forall ((x_34 list_0) (x_35 list_0) (x_4 Nat_0) (y_4 list_0))
	(=>	(and (take_0 x_34 x_4 y_4)
			(drop_0 x_35 x_4 y_4))
		(splitAt_0 (pair_1 x_34 x_35) x_4 y_4))))
(declare-fun count_0 (Nat_0 Nat_0 list_0) Bool)
(assert (forall ((x_36 Nat_0) (x_37 Nat_0) (ys_0 list_0) (x_5 Nat_0))
	(=>	(and (count_0 x_37 x_5 ys_0)
			(add_0 x_36 (Z_6 Z_5) x_37))
		(count_0 x_36 x_5 (cons_0 x_5 ys_0)))))
(assert (forall ((x_38 Nat_0) (z_2 Nat_0) (ys_0 list_0) (x_5 Nat_0))
	(=>	(and (diseqNat_0 x_5 z_2)
			(count_0 x_38 x_5 ys_0))
		(count_0 x_38 x_5 (cons_0 z_2 ys_0)))))
(assert (forall ((x_5 Nat_0))
	(count_0 Z_5 x_5 nil_0)))
(declare-fun x_6 (list_0 list_0 list_0) Bool)
(assert (forall ((x_42 list_0) (z_3 Nat_0) (xs_2 list_0) (y_6 list_0))
	(=> (x_6 x_42 xs_2 y_6)
	    (x_6 (cons_0 z_3 x_42) (cons_0 z_3 xs_2) y_6))))
(assert (forall ((x_43 list_0))
	(x_6 x_43 nil_0 x_43)))
(declare-fun stoogesort_0 (list_0 list_0) Bool)
(declare-fun stoogesort_1 (list_0 list_0) Bool)
(declare-fun stoogesort_2 (list_0 list_0) Bool)
(assert (forall ((x_70 Nat_0) (x_71 Nat_0) (x_72 Nat_0) (x_46 list_0) (x_47 list_0) (x_44 Nat_0) (ys_1 list_0) (zs_0 list_0) (x_11 list_0))
	(=>	(and (stoogesort_1 x_47 ys_1)
			(x_6 x_46 x_47 zs_0)
			(length_0 x_44 x_11)
			(splitAt_0 (pair_1 ys_1 zs_0) x_72 x_11)
			(mult_0 x_70 (Z_6 (Z_6 Z_5)) x_44)
			(add_0 x_71 x_70 (Z_6 Z_5))
			(div_0 x_72 x_71 (Z_6 (Z_6 (Z_6 Z_5)))))
		(stoogesort_0 x_46 x_11))))
(assert (forall ((x_49 list_0) (x_50 list_0) (x_51 list_0) (x_14 Nat_0) (x_15 list_0) (y_8 Nat_0) (y_7 Nat_0))
	(=>	(and (stoogesort_0 x_50 (cons_0 y_7 (cons_0 y_8 (cons_0 x_14 x_15))))
			(stoogesort_2 x_51 x_50)
			(stoogesort_0 x_49 x_51))
		(stoogesort_1 x_49 (cons_0 y_7 (cons_0 y_8 (cons_0 x_14 x_15)))))))
(assert (forall ((x_53 list_0) (y_8 Nat_0) (y_7 Nat_0))
	(=> (sort_0 x_53 y_7 y_8)
	    (stoogesort_1 x_53 (cons_0 y_7 (cons_0 y_8 nil_0))))))
(assert (forall ((y_7 Nat_0))
	(stoogesort_1 (cons_0 y_7 nil_0) (cons_0 y_7 nil_0))))
(assert (stoogesort_1 nil_0 nil_0))
(assert (forall ((x_73 Nat_0) (x_59 list_0) (x_60 list_0) (x_57 Nat_0) (ys_2 list_0) (zs_1 list_0) (x_16 list_0))
	(=>	(and (stoogesort_1 x_60 zs_1)
			(x_6 x_59 ys_2 x_60)
			(length_0 x_57 x_16)
			(splitAt_0 (pair_1 ys_2 zs_1) x_73 x_16)
			(div_0 x_73 x_57 (Z_6 (Z_6 (Z_6 Z_5)))))
		(stoogesort_2 x_59 x_16))))
(assert (forall ((x_62 list_0) (x_63 Nat_0) (x_64 Nat_0) (x_17 Nat_0) (xs_3 list_0))
	(=>	(and (diseqNat_0 x_63 x_64)
			(stoogesort_1 x_62 xs_3)
			(count_0 x_63 x_17 x_62)
			(count_0 x_64 x_17 xs_3))
		false)))
(check-sat)
