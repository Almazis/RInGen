(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_5 ) (Z_6 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_52 Nat_0))
	(unS_1 x_52 (Z_6 x_52))))
(assert (isZ_2 Z_5))
(assert (forall ((x_54 Nat_0))
	(isZ_3 (Z_6 x_54))))
(assert (forall ((x_55 Nat_0))
	(diseqNat_0 Z_5 (Z_6 x_55))))
(assert (forall ((x_56 Nat_0))
	(diseqNat_0 (Z_6 x_56) Z_5)))
(assert (forall ((x_57 Nat_0) (x_58 Nat_0))
	(=> (diseqNat_0 x_57 x_58)
	    (diseqNat_0 (Z_6 x_57) (Z_6 x_58)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_7 Nat_0))
	(add_0 y_7 Z_5 y_7)))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_7 Nat_0))
	(=> (add_0 r_0 x_46 y_7)
	    (add_0 (Z_6 r_0) (Z_6 x_46) y_7))))
(assert (forall ((y_7 Nat_0))
	(minus_0 Z_5 Z_5 y_7)))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_7 Nat_0))
	(=> (minus_0 r_0 x_46 y_7)
	    (minus_0 (Z_6 r_0) (Z_6 x_46) y_7))))
(assert (forall ((y_7 Nat_0))
	(le_0 Z_5 y_7)))
(assert (forall ((x_46 Nat_0) (y_7 Nat_0))
	(=> (le_0 x_46 y_7)
	    (le_0 (Z_6 x_46) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(ge_0 y_7 Z_5)))
(assert (forall ((x_46 Nat_0) (y_7 Nat_0))
	(=> (ge_0 x_46 y_7)
	    (ge_0 (Z_6 x_46) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(lt_0 Z_5 (Z_6 y_7))))
(assert (forall ((x_46 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_46 y_7)
	    (lt_0 (Z_6 x_46) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(gt_0 (Z_6 y_7) Z_5)))
(assert (forall ((x_46 Nat_0) (y_7 Nat_0))
	(=> (gt_0 x_46 y_7)
	    (gt_0 (Z_6 x_46) (Z_6 y_7)))))
(assert (forall ((y_7 Nat_0))
	(mult_0 Z_5 Z_5 y_7)))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_7 Nat_0) (z_7 Nat_0))
	(=>	(and (mult_0 r_0 x_46 y_7)
			(add_0 z_7 r_0 y_7))
		(mult_0 z_7 (Z_6 x_46) y_7))))
(assert (forall ((x_46 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_46 y_7)
	    (div_0 Z_5 x_46 y_7))))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_7 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_46 y_7)
			(minus_0 z_7 x_46 y_7)
			(div_0 r_0 z_7 y_7))
		(div_0 (Z_6 r_0) x_46 y_7))))
(assert (forall ((x_46 Nat_0) (y_7 Nat_0))
	(=> (lt_0 x_46 y_7)
	    (mod_0 x_46 x_46 y_7))))
(assert (forall ((r_0 Nat_0) (x_46 Nat_0) (y_7 Nat_0) (z_7 Nat_0))
	(=>	(and (ge_0 x_46 y_7)
			(minus_0 z_7 x_46 y_7)
			(mod_0 r_0 z_7 y_7))
		(mod_0 r_0 x_46 y_7))))
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
(assert (forall ((x_62 Nat_0) (x_63 list_0))
	(head_1 x_62 (cons_0 x_62 x_63))))
(assert (forall ((x_62 Nat_0) (x_63 list_0))
	(tail_1 x_63 (cons_0 x_62 x_63))))
(assert (isnil_0 nil_0))
(assert (forall ((x_65 Nat_0) (x_66 list_0))
	(iscons_0 (cons_0 x_65 x_66))))
(assert (forall ((x_67 Nat_0) (x_68 list_0))
	(diseqlist_0 nil_0 (cons_0 x_67 x_68))))
(assert (forall ((x_69 Nat_0) (x_70 list_0))
	(diseqlist_0 (cons_0 x_69 x_70) nil_0)))
(assert (forall ((x_71 Nat_0) (x_72 list_0) (x_73 Nat_0) (x_74 list_0))
	(=> (diseqNat_0 x_71 x_73)
	    (diseqlist_0 (cons_0 x_71 x_72) (cons_0 x_73 x_74)))))
(assert (forall ((x_71 Nat_0) (x_72 list_0) (x_73 Nat_0) (x_74 list_0))
	(=> (diseqlist_0 x_72 x_74)
	    (diseqlist_0 (cons_0 x_71 x_72) (cons_0 x_73 x_74)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_47 Nat_0) (x_13 list_0) (z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=>	(and (gt_0 x_0 Z_5)
			(take_0 x_13 x_47 xs_0)
			(minus_0 x_47 x_0 (Z_6 Z_5)))
		(take_0 (cons_0 z_0 x_13) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_5)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_0 Nat_0))
	(=> (gt_0 x_0 Z_5)
	    (take_0 nil_0 x_0 nil_0))))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_16 Bool_0) (y_2 Nat_0) (xs_1 list_0) (y_1 Nat_0))
	(=>	(and (le_0 y_1 y_2)
			(ordered_0 x_16 (cons_0 y_2 xs_1)))
		(ordered_0 x_16 (cons_0 y_1 (cons_0 y_2 xs_1))))))
(assert (forall ((y_2 Nat_0) (xs_1 list_0) (y_1 Nat_0))
	(=> (gt_0 y_1 y_2)
	    (ordered_0 false_0 (cons_0 y_1 (cons_0 y_2 xs_1))))))
(assert (forall ((y_1 Nat_0))
	(ordered_0 true_0 (cons_0 y_1 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun lmerge_0 (list_0 list_0 list_0) Bool)
(assert (forall ((x_22 list_0) (x_4 Nat_0) (x_5 list_0) (z_2 Nat_0) (x_3 list_0))
	(=>	(and (le_0 z_2 x_4)
			(lmerge_0 x_22 x_3 (cons_0 x_4 x_5)))
		(lmerge_0 (cons_0 z_2 x_22) (cons_0 z_2 x_3) (cons_0 x_4 x_5)))))
(assert (forall ((x_24 list_0) (x_4 Nat_0) (x_5 list_0) (z_2 Nat_0) (x_3 list_0))
	(=>	(and (gt_0 z_2 x_4)
			(lmerge_0 x_24 (cons_0 z_2 x_3) x_5))
		(lmerge_0 (cons_0 x_4 x_24) (cons_0 z_2 x_3) (cons_0 x_4 x_5)))))
(assert (forall ((z_2 Nat_0) (x_3 list_0))
	(lmerge_0 (cons_0 z_2 x_3) (cons_0 z_2 x_3) nil_0)))
(assert (forall ((x_26 list_0))
	(lmerge_0 x_26 nil_0 x_26)))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_27 Nat_0) (x_28 Nat_0) (y_4 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_28 l_0)
			(add_0 x_27 (Z_6 Z_5) x_28))
		(length_0 x_27 (cons_0 y_4 l_0)))))
(assert (length_0 Z_5 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_30 list_0) (x_7 Nat_0))
	(=> (le_0 x_7 Z_5)
	    (drop_0 x_30 x_7 x_30))))
(assert (forall ((x_49 Nat_0) (x_31 list_0) (z_3 Nat_0) (xs_2 list_0) (x_7 Nat_0))
	(=>	(and (gt_0 x_7 Z_5)
			(drop_0 x_31 x_49 xs_2)
			(minus_0 x_49 x_7 (Z_6 Z_5)))
		(drop_0 x_31 x_7 (cons_0 z_3 xs_2)))))
(assert (forall ((x_33 list_0) (x_7 Nat_0))
	(=> (le_0 x_7 Z_5)
	    (drop_0 x_33 x_7 x_33))))
(assert (forall ((x_7 Nat_0))
	(=> (gt_0 x_7 Z_5)
	    (drop_0 nil_0 x_7 nil_0))))
(declare-fun msorttd_0 (list_0 list_0) Bool)
(assert (forall ((x_36 list_0) (x_37 list_0) (x_38 list_0) (x_39 list_0) (x_40 list_0) (x_35 Nat_0) (k_0 Nat_0) (x_9 Nat_0) (x_10 list_0) (y_6 Nat_0))
	(=>	(and (take_0 x_37 k_0 (cons_0 y_6 (cons_0 x_9 x_10)))
			(msorttd_0 x_38 x_37)
			(drop_0 x_39 k_0 (cons_0 y_6 (cons_0 x_9 x_10)))
			(msorttd_0 x_40 x_39)
			(lmerge_0 x_36 x_38 x_40)
			(length_0 x_35 (cons_0 y_6 (cons_0 x_9 x_10)))
			(div_0 k_0 x_35 (Z_6 (Z_6 Z_5))))
		(msorttd_0 x_36 (cons_0 y_6 (cons_0 x_9 x_10))))))
(assert (forall ((y_6 Nat_0))
	(msorttd_0 (cons_0 y_6 nil_0) (cons_0 y_6 nil_0))))
(assert (msorttd_0 nil_0 nil_0))
(assert (forall ((x_44 list_0) (x_45 Bool_0) (xs_3 list_0))
	(=>	(and (diseqBool_0 x_45 true_0)
			(msorttd_0 x_44 xs_3)
			(ordered_0 x_45 x_44))
		false)))
(check-sat)
