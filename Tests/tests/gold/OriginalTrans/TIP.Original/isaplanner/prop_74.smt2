(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_5 ) (Z_6 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_65 Nat_1))
	(unS_1 x_65 (Z_6 x_65))))
(assert (isZ_3 Z_5))
(assert (forall ((x_67 Nat_1))
	(isZ_4 (Z_6 x_67))))
(assert (forall ((x_68 Nat_1))
	(diseqNat_1 Z_5 (Z_6 x_68))))
(assert (forall ((x_69 Nat_1))
	(diseqNat_1 (Z_6 x_69) Z_5)))
(assert (forall ((x_70 Nat_1) (x_71 Nat_1))
	(=> (diseqNat_1 x_70 x_71)
	    (diseqNat_1 (Z_6 x_70) (Z_6 x_71)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_6 Nat_1))
	(add_0 y_6 Z_5 y_6)))
(assert (forall ((r_0 Nat_1) (x_41 Nat_1) (y_6 Nat_1))
	(=> (add_0 r_0 x_41 y_6)
	    (add_0 (Z_6 r_0) (Z_6 x_41) y_6))))
(assert (forall ((y_6 Nat_1))
	(minus_0 Z_5 Z_5 y_6)))
(assert (forall ((r_0 Nat_1) (x_41 Nat_1) (y_6 Nat_1))
	(=> (minus_0 r_0 x_41 y_6)
	    (minus_0 (Z_6 r_0) (Z_6 x_41) y_6))))
(assert (forall ((y_6 Nat_1))
	(le_0 Z_5 y_6)))
(assert (forall ((x_41 Nat_1) (y_6 Nat_1))
	(=> (le_0 x_41 y_6)
	    (le_0 (Z_6 x_41) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(ge_0 y_6 Z_5)))
(assert (forall ((x_41 Nat_1) (y_6 Nat_1))
	(=> (ge_0 x_41 y_6)
	    (ge_0 (Z_6 x_41) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(lt_0 Z_5 (Z_6 y_6))))
(assert (forall ((x_41 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_41 y_6)
	    (lt_0 (Z_6 x_41) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(gt_0 (Z_6 y_6) Z_5)))
(assert (forall ((x_41 Nat_1) (y_6 Nat_1))
	(=> (gt_0 x_41 y_6)
	    (gt_0 (Z_6 x_41) (Z_6 y_6)))))
(assert (forall ((y_6 Nat_1))
	(mult_0 Z_5 Z_5 y_6)))
(assert (forall ((r_0 Nat_1) (x_41 Nat_1) (y_6 Nat_1) (z_7 Nat_1))
	(=>	(and (mult_0 r_0 x_41 y_6)
			(add_0 z_7 r_0 y_6))
		(mult_0 z_7 (Z_6 x_41) y_6))))
(assert (forall ((x_41 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_41 y_6)
	    (div_0 Z_5 x_41 y_6))))
(assert (forall ((r_0 Nat_1) (x_41 Nat_1) (y_6 Nat_1) (z_7 Nat_1))
	(=>	(and (ge_0 x_41 y_6)
			(minus_0 z_7 x_41 y_6)
			(div_0 r_0 z_7 y_6))
		(div_0 (Z_6 r_0) x_41 y_6))))
(assert (forall ((x_41 Nat_1) (y_6 Nat_1))
	(=> (lt_0 x_41 y_6)
	    (mod_0 x_41 x_41 y_6))))
(assert (forall ((r_0 Nat_1) (x_41 Nat_1) (y_6 Nat_1) (z_7 Nat_1))
	(=>	(and (ge_0 x_41 y_6)
			(minus_0 z_7 x_41 y_6)
			(mod_0 r_0 z_7 y_6))
		(mod_0 r_0 x_41 y_6))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_1) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_1 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_43 Nat_1) (x_44 list_0))
	(head_1 x_43 (cons_0 x_43 x_44))))
(assert (forall ((x_43 Nat_1) (x_44 list_0))
	(tail_1 x_44 (cons_0 x_43 x_44))))
(assert (isnil_0 nil_0))
(assert (forall ((x_46 Nat_1) (x_47 list_0))
	(iscons_0 (cons_0 x_46 x_47))))
(assert (forall ((x_48 Nat_1) (x_49 list_0))
	(diseqlist_0 nil_0 (cons_0 x_48 x_49))))
(assert (forall ((x_50 Nat_1) (x_51 list_0))
	(diseqlist_0 (cons_0 x_50 x_51) nil_0)))
(assert (forall ((x_52 Nat_1) (x_53 list_0) (x_54 Nat_1) (x_55 list_0))
	(=> (diseqNat_1 x_52 x_54)
	    (diseqlist_0 (cons_0 x_52 x_53) (cons_0 x_54 x_55)))))
(assert (forall ((x_52 Nat_1) (x_53 list_0) (x_54 Nat_1) (x_55 list_0))
	(=> (diseqlist_0 x_53 x_55)
	    (diseqlist_0 (cons_0 x_52 x_53) (cons_0 x_54 x_55)))))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_57 Nat_0))
	(projS_1 x_57 (S_0 x_57))))
(assert (isZ_2 Z_0))
(assert (forall ((x_59 Nat_0))
	(isS_0 (S_0 x_59))))
(assert (forall ((x_60 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_60))))
(assert (forall ((x_61 Nat_0))
	(diseqNat_0 (S_0 x_61) Z_0)))
(assert (forall ((x_62 Nat_0) (x_63 Nat_0))
	(=> (diseqNat_0 x_62 x_63)
	    (diseqNat_0 (S_0 x_62) (S_0 x_63)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_14 list_0) (x_1 Nat_1) (x_2 list_0) (z_1 Nat_0))
	(=> (take_0 x_14 z_1 x_2)
	    (take_0 (cons_0 x_1 x_14) (S_0 z_1) (cons_0 x_1 x_2)))))
(assert (forall ((z_1 Nat_0))
	(take_0 nil_0 (S_0 z_1) nil_0)))
(assert (forall ((y_0 list_0))
	(take_0 nil_0 Z_0 y_0)))
(declare-fun len_0 (Nat_0 list_0) Bool)
(assert (forall ((x_18 Nat_0) (y_1 Nat_1) (xs_0 list_0))
	(=> (len_0 x_18 xs_0)
	    (len_0 (S_0 x_18) (cons_0 y_1 xs_0)))))
(assert (len_0 Z_0 nil_0))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_20 list_0) (x_5 Nat_1) (x_6 list_0) (z_2 Nat_0))
	(=> (drop_0 x_20 z_2 x_6)
	    (drop_0 x_20 (S_0 z_2) (cons_0 x_5 x_6)))))
(assert (forall ((z_2 Nat_0))
	(drop_0 nil_0 (S_0 z_2) nil_0)))
(assert (forall ((x_23 list_0))
	(drop_0 x_23 Z_0 x_23)))
(declare-fun x_7 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_24 Nat_0) (x_9 Nat_0) (z_3 Nat_0))
	(=> (x_7 x_24 z_3 x_9)
	    (x_7 x_24 (S_0 z_3) (S_0 x_9)))))
(assert (forall ((z_3 Nat_0))
	(x_7 (S_0 z_3) (S_0 z_3) Z_0)))
(assert (forall ((y_3 Nat_0))
	(x_7 Z_0 Z_0 y_3)))
(declare-fun x_10 (list_0 list_0 list_0) Bool)
(assert (forall ((x_29 list_0) (z_4 Nat_1) (xs_1 list_0) (y_4 list_0))
	(=> (x_10 x_29 xs_1 y_4)
	    (x_10 (cons_0 z_4 x_29) (cons_0 z_4 xs_1) y_4))))
(assert (forall ((x_30 list_0))
	(x_10 x_30 nil_0 x_30)))
(declare-fun rev_0 (list_0 list_0) Bool)
(assert (forall ((x_31 list_0) (x_32 list_0) (y_5 Nat_1) (xs_2 list_0))
	(=>	(and (rev_0 x_32 xs_2)
			(x_10 x_31 x_32 (cons_0 y_5 nil_0)))
		(rev_0 x_31 (cons_0 y_5 xs_2)))))
(assert (rev_0 nil_0 nil_0))
(assert (forall ((x_35 list_0) (x_36 list_0) (x_37 Nat_0) (x_38 Nat_0) (x_39 list_0) (x_40 list_0) (i_0 Nat_0) (xs_3 list_0))
	(=>	(and (diseqlist_0 x_36 x_40)
			(take_0 x_35 i_0 xs_3)
			(rev_0 x_36 x_35)
			(len_0 x_37 xs_3)
			(x_7 x_38 x_37 i_0)
			(rev_0 x_39 xs_3)
			(drop_0 x_40 x_38 x_39))
		false)))
(check-sat)
