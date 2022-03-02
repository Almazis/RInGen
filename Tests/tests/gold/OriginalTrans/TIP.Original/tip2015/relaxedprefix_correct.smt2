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
(assert (forall ((x_53 Bool_0) (x_54 list_0))
	(head_3 x_53 (cons_0 x_53 x_54))))
(assert (forall ((x_53 Bool_0) (x_54 list_0))
	(tail_3 x_54 (cons_0 x_53 x_54))))
(assert (isnil_0 nil_0))
(assert (forall ((x_56 Bool_0) (x_57 list_0))
	(iscons_0 (cons_0 x_56 x_57))))
(assert (forall ((x_58 Bool_0) (x_59 list_0))
	(diseqlist_0 nil_0 (cons_0 x_58 x_59))))
(assert (forall ((x_60 Bool_0) (x_61 list_0))
	(diseqlist_0 (cons_0 x_60 x_61) nil_0)))
(assert (forall ((x_62 Bool_0) (x_63 list_0) (x_64 Bool_0) (x_65 list_0))
	(=> (diseqBool_0 x_62 x_64)
	    (diseqlist_0 (cons_0 x_62 x_63) (cons_0 x_64 x_65)))))
(assert (forall ((x_62 Bool_0) (x_63 list_0) (x_64 Bool_0) (x_65 list_0))
	(=> (diseqlist_0 x_63 x_65)
	    (diseqlist_0 (cons_0 x_62 x_63) (cons_0 x_64 x_65)))))
(declare-datatypes ((It_0 0)) (((A_0 ) (B_0 ) (C_0 ))))
(declare-fun diseqIt_0 (It_0 It_0) Bool)
(declare-fun isA_0 (It_0) Bool)
(declare-fun isB_0 (It_0) Bool)
(declare-fun isC_0 (It_0) Bool)
(assert (isA_0 A_0))
(assert (isB_0 B_0))
(assert (isC_0 C_0))
(assert (diseqIt_0 A_0 B_0))
(assert (diseqIt_0 A_0 C_0))
(assert (diseqIt_0 B_0 A_0))
(assert (diseqIt_0 C_0 A_0))
(assert (diseqIt_0 B_0 C_0))
(assert (diseqIt_0 C_0 B_0))
(declare-datatypes ((list_1 0)) (((nil_1 ) (cons_1 (head_1 It_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_4 (It_0 list_1) Bool)
(declare-fun tail_4 (list_1 list_1) Bool)
(declare-fun isnil_1 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_70 It_0) (x_71 list_1))
	(head_4 x_70 (cons_1 x_70 x_71))))
(assert (forall ((x_70 It_0) (x_71 list_1))
	(tail_4 x_71 (cons_1 x_70 x_71))))
(assert (isnil_1 nil_1))
(assert (forall ((x_73 It_0) (x_74 list_1))
	(iscons_1 (cons_1 x_73 x_74))))
(assert (forall ((x_75 It_0) (x_76 list_1))
	(diseqlist_1 nil_1 (cons_1 x_75 x_76))))
(assert (forall ((x_77 It_0) (x_78 list_1))
	(diseqlist_1 (cons_1 x_77 x_78) nil_1)))
(assert (forall ((x_79 It_0) (x_80 list_1) (x_81 It_0) (x_82 list_1))
	(=> (diseqIt_0 x_79 x_81)
	    (diseqlist_1 (cons_1 x_79 x_80) (cons_1 x_81 x_82)))))
(assert (forall ((x_79 It_0) (x_80 list_1) (x_81 It_0) (x_82 list_1))
	(=> (diseqlist_1 x_80 x_82)
	    (diseqlist_1 (cons_1 x_79 x_80) (cons_1 x_81 x_82)))))
(declare-datatypes ((list_2 0)) (((nil_2 ) (cons_2 (head_2 list_1) (tail_2 list_2)))))
(declare-fun diseqlist_2 (list_2 list_2) Bool)
(declare-fun head_5 (list_1 list_2) Bool)
(declare-fun tail_5 (list_2 list_2) Bool)
(declare-fun isnil_2 (list_2) Bool)
(declare-fun iscons_2 (list_2) Bool)
(assert (forall ((x_84 list_1) (x_85 list_2))
	(head_5 x_84 (cons_2 x_84 x_85))))
(assert (forall ((x_84 list_1) (x_85 list_2))
	(tail_5 x_85 (cons_2 x_84 x_85))))
(assert (isnil_2 nil_2))
(assert (forall ((x_87 list_1) (x_88 list_2))
	(iscons_2 (cons_2 x_87 x_88))))
(assert (forall ((x_89 list_1) (x_90 list_2))
	(diseqlist_2 nil_2 (cons_2 x_89 x_90))))
(assert (forall ((x_91 list_1) (x_92 list_2))
	(diseqlist_2 (cons_2 x_91 x_92) nil_2)))
(assert (forall ((x_93 list_1) (x_94 list_2) (x_95 list_1) (x_96 list_2))
	(=> (diseqlist_1 x_93 x_95)
	    (diseqlist_2 (cons_2 x_93 x_94) (cons_2 x_95 x_96)))))
(assert (forall ((x_93 list_1) (x_94 list_2) (x_95 list_1) (x_96 list_2))
	(=> (diseqlist_2 x_94 x_96)
	    (diseqlist_2 (cons_2 x_93 x_94) (cons_2 x_95 x_96)))))
(declare-fun removeOne_0 (list_2 It_0 list_2) Bool)
(assert (forall ((x_17 list_2) (z_0 list_1) (x_1 list_2) (x_0 It_0))
	(=> (removeOne_0 x_17 x_0 x_1)
	    (removeOne_0 (cons_2 (cons_1 x_0 z_0) x_17) x_0 (cons_2 z_0 x_1)))))
(assert (forall ((x_0 It_0))
	(removeOne_0 nil_2 x_0 nil_2)))
(declare-fun removeOne_1 (list_2 list_1) Bool)
(assert (forall ((x_20 list_2) (x_21 list_2) (y_1 It_0) (xs_0 list_1))
	(=>	(and (removeOne_1 x_20 xs_0)
			(removeOne_0 x_21 y_1 x_20))
		(removeOne_1 (cons_2 xs_0 x_21) (cons_1 y_1 xs_0)))))
(assert (removeOne_1 nil_2 nil_1))
(declare-fun or_0 (Bool_0 list_0) Bool)
(assert (forall ((x_23 Bool_0) (x_24 Bool_0) (y_2 Bool_0) (xs_1 list_0))
	(=>	(and (or_0 x_24 xs_1)
			(or_1 x_23 y_2 x_24))
		(or_0 x_23 (cons_0 y_2 xs_1)))))
(assert (or_0 false_0 nil_0))
(declare-fun isPrefix_0 (Bool_0 list_1 list_1) Bool)
(assert (forall ((x_26 Bool_0) (x_6 It_0) (x_7 list_1) (x_5 list_1))
	(=> (isPrefix_0 x_26 x_5 x_7)
	    (isPrefix_0 x_26 (cons_1 x_6 x_5) (cons_1 x_6 x_7)))))
(assert (forall ((x_6 It_0) (x_7 list_1) (z_1 It_0) (x_5 list_1))
	(=> (diseqIt_0 z_1 x_6)
	    (isPrefix_0 false_0 (cons_1 z_1 x_5) (cons_1 x_6 x_7)))))
(assert (forall ((z_1 It_0) (x_5 list_1))
	(isPrefix_0 false_0 (cons_1 z_1 x_5) nil_1)))
(assert (forall ((y_3 list_1))
	(isPrefix_0 true_0 nil_1 y_3)))
(declare-fun isRelaxedPrefix_0 (Bool_0 list_1 list_1) Bool)
(assert (forall ((x_31 Bool_0) (x_12 It_0) (x_13 list_1) (x_10 It_0) (x_11 list_1))
	(=> (isRelaxedPrefix_0 x_31 (cons_1 x_10 x_11) x_13)
	    (isRelaxedPrefix_0 x_31 (cons_1 x_12 (cons_1 x_10 x_11)) (cons_1 x_12 x_13)))))
(assert (forall ((x_33 Bool_0) (x_12 It_0) (x_13 list_1) (x_10 It_0) (x_11 list_1) (z_2 It_0))
	(=>	(and (diseqIt_0 z_2 x_12)
			(isPrefix_0 x_33 (cons_1 x_10 x_11) (cons_1 x_12 x_13)))
		(isRelaxedPrefix_0 x_33 (cons_1 z_2 (cons_1 x_10 x_11)) (cons_1 x_12 x_13)))))
(assert (forall ((x_10 It_0) (x_11 list_1) (z_2 It_0))
	(isRelaxedPrefix_0 false_0 (cons_1 z_2 (cons_1 x_10 x_11)) nil_1)))
(assert (forall ((z_2 It_0) (y_4 list_1))
	(isRelaxedPrefix_0 true_0 (cons_1 z_2 nil_1) y_4)))
(assert (forall ((y_4 list_1))
	(isRelaxedPrefix_0 true_0 nil_1 y_4)))
(declare-fun spec_0 (list_0 list_1 list_2) Bool)
(assert (forall ((x_39 Bool_0) (x_40 list_0) (y_5 list_1) (z_3 list_2) (ys_0 list_1))
	(=>	(and (isPrefix_0 x_39 y_5 ys_0)
			(spec_0 x_40 ys_0 z_3))
		(spec_0 (cons_0 x_39 x_40) ys_0 (cons_2 y_5 z_3)))))
(assert (forall ((ys_0 list_1))
	(spec_0 nil_0 ys_0 nil_2)))
(declare-fun spec_1 (Bool_0 list_1 list_1) Bool)
(assert (forall ((x_42 Bool_0) (x_43 list_2) (x_44 list_0) (x_15 list_1) (y_6 list_1))
	(=>	(and (removeOne_1 x_43 x_15)
			(spec_0 x_44 y_6 (cons_2 x_15 x_43))
			(or_0 x_42 x_44))
		(spec_1 x_42 x_15 y_6))))
(assert (forall ((x_46 Bool_0) (x_47 Bool_0) (xs_2 list_1) (ys_1 list_1))
	(=>	(and (diseqBool_0 x_46 x_47)
			(isRelaxedPrefix_0 x_46 xs_2 ys_1)
			(spec_1 x_47 xs_2 ys_1))
		false)))
(check-sat)
