(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_2 ) (Z_3 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_43 Nat_0))
	(unS_1 x_43 (Z_3 x_43))))
(assert (isZ_2 Z_2))
(assert (forall ((x_45 Nat_0))
	(isZ_3 (Z_3 x_45))))
(assert (forall ((x_46 Nat_0))
	(diseqNat_0 Z_2 (Z_3 x_46))))
(assert (forall ((x_47 Nat_0))
	(diseqNat_0 (Z_3 x_47) Z_2)))
(assert (forall ((x_48 Nat_0) (x_49 Nat_0))
	(=> (diseqNat_0 x_48 x_49)
	    (diseqNat_0 (Z_3 x_48) (Z_3 x_49)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_6 Nat_0))
	(add_0 y_6 Z_2 y_6)))
(assert (forall ((r_0 Nat_0) (x_41 Nat_0) (y_6 Nat_0))
	(=> (add_0 r_0 x_41 y_6)
	    (add_0 (Z_3 r_0) (Z_3 x_41) y_6))))
(assert (forall ((y_6 Nat_0))
	(minus_0 Z_2 Z_2 y_6)))
(assert (forall ((r_0 Nat_0) (x_41 Nat_0) (y_6 Nat_0))
	(=> (minus_0 r_0 x_41 y_6)
	    (minus_0 (Z_3 r_0) (Z_3 x_41) y_6))))
(assert (forall ((y_6 Nat_0))
	(le_0 Z_2 y_6)))
(assert (forall ((x_41 Nat_0) (y_6 Nat_0))
	(=> (le_0 x_41 y_6)
	    (le_0 (Z_3 x_41) (Z_3 y_6)))))
(assert (forall ((y_6 Nat_0))
	(ge_0 y_6 Z_2)))
(assert (forall ((x_41 Nat_0) (y_6 Nat_0))
	(=> (ge_0 x_41 y_6)
	    (ge_0 (Z_3 x_41) (Z_3 y_6)))))
(assert (forall ((y_6 Nat_0))
	(lt_0 Z_2 (Z_3 y_6))))
(assert (forall ((x_41 Nat_0) (y_6 Nat_0))
	(=> (lt_0 x_41 y_6)
	    (lt_0 (Z_3 x_41) (Z_3 y_6)))))
(assert (forall ((y_6 Nat_0))
	(gt_0 (Z_3 y_6) Z_2)))
(assert (forall ((x_41 Nat_0) (y_6 Nat_0))
	(=> (gt_0 x_41 y_6)
	    (gt_0 (Z_3 x_41) (Z_3 y_6)))))
(assert (forall ((y_6 Nat_0))
	(mult_0 Z_2 Z_2 y_6)))
(assert (forall ((r_0 Nat_0) (x_41 Nat_0) (y_6 Nat_0) (z_4 Nat_0))
	(=>	(and (mult_0 r_0 x_41 y_6)
			(add_0 z_4 r_0 y_6))
		(mult_0 z_4 (Z_3 x_41) y_6))))
(assert (forall ((x_41 Nat_0) (y_6 Nat_0))
	(=> (lt_0 x_41 y_6)
	    (div_0 Z_2 x_41 y_6))))
(assert (forall ((r_0 Nat_0) (x_41 Nat_0) (y_6 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_41 y_6)
			(minus_0 z_4 x_41 y_6)
			(div_0 r_0 z_4 y_6))
		(div_0 (Z_3 r_0) x_41 y_6))))
(assert (forall ((x_41 Nat_0) (y_6 Nat_0))
	(=> (lt_0 x_41 y_6)
	    (mod_0 x_41 x_41 y_6))))
(assert (forall ((r_0 Nat_0) (x_41 Nat_0) (y_6 Nat_0) (z_4 Nat_0))
	(=>	(and (ge_0 x_41 y_6)
			(minus_0 z_4 x_41 y_6)
			(mod_0 r_0 z_4 y_6))
		(mod_0 r_0 x_41 y_6))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_1 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_51 Nat_0) (x_52 list_0))
	(head_1 x_51 (cons_0 x_51 x_52))))
(assert (forall ((x_51 Nat_0) (x_52 list_0))
	(tail_1 x_52 (cons_0 x_51 x_52))))
(assert (isnil_0 nil_0))
(assert (forall ((x_54 Nat_0) (x_55 list_0))
	(iscons_0 (cons_0 x_54 x_55))))
(assert (forall ((x_56 Nat_0) (x_57 list_0))
	(diseqlist_0 nil_0 (cons_0 x_56 x_57))))
(assert (forall ((x_58 Nat_0) (x_59 list_0))
	(diseqlist_0 (cons_0 x_58 x_59) nil_0)))
(assert (forall ((x_60 Nat_0) (x_61 list_0) (x_62 Nat_0) (x_63 list_0))
	(=> (diseqNat_0 x_60 x_62)
	    (diseqlist_0 (cons_0 x_60 x_61) (cons_0 x_62 x_63)))))
(assert (forall ((x_60 Nat_0) (x_61 list_0) (x_62 Nat_0) (x_63 list_0))
	(=> (diseqlist_0 x_61 x_63)
	    (diseqlist_0 (cons_0 x_60 x_61) (cons_0 x_62 x_63)))))
(declare-datatypes ((Heap_0 0)) (((Node_0 (projNode_0 Heap_0) (projNode_1 Nat_0) (projNode_2 Heap_0)) (Nil_1 ))))
(declare-fun diseqHeap_0 (Heap_0 Heap_0) Bool)
(declare-fun projNode_3 (Heap_0 Heap_0) Bool)
(declare-fun projNode_4 (Nat_0 Heap_0) Bool)
(declare-fun projNode_5 (Heap_0 Heap_0) Bool)
(declare-fun isNode_0 (Heap_0) Bool)
(declare-fun isNil_1 (Heap_0) Bool)
(assert (forall ((x_64 Heap_0) (x_65 Nat_0) (x_66 Heap_0))
	(projNode_3 x_64 (Node_0 x_64 x_65 x_66))))
(assert (forall ((x_64 Heap_0) (x_65 Nat_0) (x_66 Heap_0))
	(projNode_4 x_65 (Node_0 x_64 x_65 x_66))))
(assert (forall ((x_64 Heap_0) (x_65 Nat_0) (x_66 Heap_0))
	(projNode_5 x_66 (Node_0 x_64 x_65 x_66))))
(assert (forall ((x_69 Heap_0) (x_70 Nat_0) (x_71 Heap_0))
	(isNode_0 (Node_0 x_69 x_70 x_71))))
(assert (isNil_1 Nil_1))
(assert (forall ((x_72 Heap_0) (x_73 Nat_0) (x_74 Heap_0))
	(diseqHeap_0 (Node_0 x_72 x_73 x_74) Nil_1)))
(assert (forall ((x_75 Heap_0) (x_76 Nat_0) (x_77 Heap_0))
	(diseqHeap_0 Nil_1 (Node_0 x_75 x_76 x_77))))
(assert (forall ((x_78 Heap_0) (x_79 Nat_0) (x_80 Heap_0) (x_81 Heap_0) (x_82 Nat_0) (x_83 Heap_0))
	(=> (diseqHeap_0 x_78 x_81)
	    (diseqHeap_0 (Node_0 x_78 x_79 x_80) (Node_0 x_81 x_82 x_83)))))
(assert (forall ((x_78 Heap_0) (x_79 Nat_0) (x_80 Heap_0) (x_81 Heap_0) (x_82 Nat_0) (x_83 Heap_0))
	(=> (diseqNat_0 x_79 x_82)
	    (diseqHeap_0 (Node_0 x_78 x_79 x_80) (Node_0 x_81 x_82 x_83)))))
(assert (forall ((x_78 Heap_0) (x_79 Nat_0) (x_80 Heap_0) (x_81 Heap_0) (x_82 Nat_0) (x_83 Heap_0))
	(=> (diseqHeap_0 x_80 x_83)
	    (diseqHeap_0 (Node_0 x_78 x_79 x_80) (Node_0 x_81 x_82 x_83)))))
(declare-fun insert_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=> (le_0 x_0 z_0)
	    (insert_0 (cons_0 x_0 (cons_0 z_0 xs_0)) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_14 list_0) (z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=>	(and (gt_0 x_0 z_0)
			(insert_0 x_14 x_0 xs_0))
		(insert_0 (cons_0 z_0 x_14) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_0 Nat_0))
	(insert_0 (cons_0 x_0 nil_0) x_0 nil_0)))
(declare-fun isort_0 (list_0 list_0) Bool)
(assert (forall ((x_16 list_0) (x_17 list_0) (y_1 Nat_0) (xs_1 list_0))
	(=>	(and (isort_0 x_17 xs_1)
			(insert_0 x_16 y_1 x_17))
		(isort_0 x_16 (cons_0 y_1 xs_1)))))
(assert (isort_0 nil_0 nil_0))
(declare-fun hmerge_0 (Heap_0 Heap_0 Heap_0) Bool)
(assert (forall ((x_20 Heap_0))
	(hmerge_0 x_20 Nil_1 x_20)))
(assert (forall ((z_1 Heap_0) (x_3 Nat_0) (x_4 Heap_0))
	(hmerge_0 (Node_0 z_1 x_3 x_4) (Node_0 z_1 x_3 x_4) Nil_1)))
(assert (forall ((x_23 Heap_0) (x_5 Heap_0) (x_6 Nat_0) (x_7 Heap_0) (z_1 Heap_0) (x_3 Nat_0) (x_4 Heap_0))
	(=>	(and (le_0 x_3 x_6)
			(hmerge_0 x_23 x_4 (Node_0 x_5 x_6 x_7)))
		(hmerge_0 (Node_0 x_23 x_3 z_1) (Node_0 z_1 x_3 x_4) (Node_0 x_5 x_6 x_7)))))
(assert (forall ((x_25 Heap_0) (x_5 Heap_0) (x_6 Nat_0) (x_7 Heap_0) (z_1 Heap_0) (x_3 Nat_0) (x_4 Heap_0))
	(=>	(and (gt_0 x_3 x_6)
			(hmerge_0 x_25 (Node_0 z_1 x_3 x_4) x_7))
		(hmerge_0 (Node_0 x_25 x_6 x_5) (Node_0 z_1 x_3 x_4) (Node_0 x_5 x_6 x_7)))))
(declare-fun toList_0 (list_0 Heap_0) Bool)
(assert (toList_0 nil_0 Nil_1))
(assert (forall ((x_28 Heap_0) (x_29 list_0) (p_0 Heap_0) (y_3 Nat_0) (q_0 Heap_0))
	(=>	(and (hmerge_0 x_28 p_0 q_0)
			(toList_0 x_29 x_28))
		(toList_0 (cons_0 y_3 x_29) (Node_0 p_0 y_3 q_0)))))
(declare-fun hinsert_0 (Heap_0 Nat_0 Heap_0) Bool)
(assert (forall ((x_30 Heap_0) (x_9 Nat_0) (y_4 Heap_0))
	(=> (hmerge_0 x_30 (Node_0 Nil_1 x_9 Nil_1) y_4)
	    (hinsert_0 x_30 x_9 y_4))))
(declare-fun toHeap_0 (Heap_0 list_0) Bool)
(assert (forall ((x_32 Heap_0) (x_33 Heap_0) (y_5 Nat_0) (xs_2 list_0))
	(=>	(and (toHeap_0 x_33 xs_2)
			(hinsert_0 x_32 y_5 x_33))
		(toHeap_0 x_32 (cons_0 y_5 xs_2)))))
(assert (toHeap_0 Nil_1 nil_0))
(declare-fun hsort_0 (list_0 list_0) Bool)
(assert (forall ((x_36 list_0) (x_37 Heap_0) (x_11 list_0))
	(=>	(and (toHeap_0 x_37 x_11)
			(toList_0 x_36 x_37))
		(hsort_0 x_36 x_11))))
(assert (forall ((x_39 list_0) (x_40 list_0) (xs_3 list_0))
	(=>	(and (diseqlist_0 x_39 x_40)
			(hsort_0 x_39 xs_3)
			(isort_0 x_40 xs_3))
		false)))
(check-sat)
