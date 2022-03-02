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
(declare-datatypes ((Nat_0 0)) (((zero_0 ) (succ_0 (p_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun p_1 (Nat_0 Nat_0) Bool)
(declare-fun iszero_0 (Nat_0) Bool)
(declare-fun issucc_0 (Nat_0) Bool)
(assert (forall ((x_63 Nat_0))
	(p_1 x_63 (succ_0 x_63))))
(assert (iszero_0 zero_0))
(assert (forall ((x_65 Nat_0))
	(issucc_0 (succ_0 x_65))))
(assert (forall ((x_66 Nat_0))
	(diseqNat_0 zero_0 (succ_0 x_66))))
(assert (forall ((x_67 Nat_0))
	(diseqNat_0 (succ_0 x_67) zero_0)))
(assert (forall ((x_68 Nat_0) (x_69 Nat_0))
	(=> (diseqNat_0 x_68 x_69)
	    (diseqNat_0 (succ_0 x_68) (succ_0 x_69)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_2 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_71 Nat_0) (x_72 list_0))
	(head_2 x_71 (cons_0 x_71 x_72))))
(assert (forall ((x_71 Nat_0) (x_72 list_0))
	(tail_2 x_72 (cons_0 x_71 x_72))))
(assert (isnil_0 nil_0))
(assert (forall ((x_74 Nat_0) (x_75 list_0))
	(iscons_0 (cons_0 x_74 x_75))))
(assert (forall ((x_76 Nat_0) (x_77 list_0))
	(diseqlist_0 nil_0 (cons_0 x_76 x_77))))
(assert (forall ((x_78 Nat_0) (x_79 list_0))
	(diseqlist_0 (cons_0 x_78 x_79) nil_0)))
(assert (forall ((x_80 Nat_0) (x_81 list_0) (x_82 Nat_0) (x_83 list_0))
	(=> (diseqNat_0 x_80 x_82)
	    (diseqlist_0 (cons_0 x_80 x_81) (cons_0 x_82 x_83)))))
(assert (forall ((x_80 Nat_0) (x_81 list_0) (x_82 Nat_0) (x_83 list_0))
	(=> (diseqlist_0 x_81 x_83)
	    (diseqlist_0 (cons_0 x_80 x_81) (cons_0 x_82 x_83)))))
(declare-datatypes ((Heap_0 0)) (((Node_0 (projNode_0 Heap_0) (projNode_1 Nat_0) (projNode_2 Heap_0)) (Nil_1 ))))
(declare-fun diseqHeap_0 (Heap_0 Heap_0) Bool)
(declare-fun projNode_3 (Heap_0 Heap_0) Bool)
(declare-fun projNode_4 (Nat_0 Heap_0) Bool)
(declare-fun projNode_5 (Heap_0 Heap_0) Bool)
(declare-fun isNode_0 (Heap_0) Bool)
(declare-fun isNil_1 (Heap_0) Bool)
(assert (forall ((x_84 Heap_0) (x_85 Nat_0) (x_86 Heap_0))
	(projNode_3 x_84 (Node_0 x_84 x_85 x_86))))
(assert (forall ((x_84 Heap_0) (x_85 Nat_0) (x_86 Heap_0))
	(projNode_4 x_85 (Node_0 x_84 x_85 x_86))))
(assert (forall ((x_84 Heap_0) (x_85 Nat_0) (x_86 Heap_0))
	(projNode_5 x_86 (Node_0 x_84 x_85 x_86))))
(assert (forall ((x_89 Heap_0) (x_90 Nat_0) (x_91 Heap_0))
	(isNode_0 (Node_0 x_89 x_90 x_91))))
(assert (isNil_1 Nil_1))
(assert (forall ((x_92 Heap_0) (x_93 Nat_0) (x_94 Heap_0))
	(diseqHeap_0 (Node_0 x_92 x_93 x_94) Nil_1)))
(assert (forall ((x_95 Heap_0) (x_96 Nat_0) (x_97 Heap_0))
	(diseqHeap_0 Nil_1 (Node_0 x_95 x_96 x_97))))
(assert (forall ((x_100 Heap_0) (x_101 Heap_0) (x_102 Nat_0) (x_103 Heap_0) (x_98 Heap_0) (x_99 Nat_0))
	(=> (diseqHeap_0 x_98 x_101)
	    (diseqHeap_0 (Node_0 x_98 x_99 x_100) (Node_0 x_101 x_102 x_103)))))
(assert (forall ((x_100 Heap_0) (x_101 Heap_0) (x_102 Nat_0) (x_103 Heap_0) (x_98 Heap_0) (x_99 Nat_0))
	(=> (diseqNat_0 x_99 x_102)
	    (diseqHeap_0 (Node_0 x_98 x_99 x_100) (Node_0 x_101 x_102 x_103)))))
(assert (forall ((x_100 Heap_0) (x_101 Heap_0) (x_102 Nat_0) (x_103 Heap_0) (x_98 Heap_0) (x_99 Nat_0))
	(=> (diseqHeap_0 x_100 x_103)
	    (diseqHeap_0 (Node_0 x_98 x_99 x_100) (Node_0 x_101 x_102 x_103)))))
(declare-datatypes ((list_1 0)) (((nil_2 ) (cons_1 (head_1 Heap_0) (tail_1 list_1)))))
(declare-fun diseqlist_1 (list_1 list_1) Bool)
(declare-fun head_3 (Heap_0 list_1) Bool)
(declare-fun tail_3 (list_1 list_1) Bool)
(declare-fun isnil_2 (list_1) Bool)
(declare-fun iscons_1 (list_1) Bool)
(assert (forall ((x_105 Heap_0) (x_106 list_1))
	(head_3 x_105 (cons_1 x_105 x_106))))
(assert (forall ((x_105 Heap_0) (x_106 list_1))
	(tail_3 x_106 (cons_1 x_105 x_106))))
(assert (isnil_2 nil_2))
(assert (forall ((x_108 Heap_0) (x_109 list_1))
	(iscons_1 (cons_1 x_108 x_109))))
(assert (forall ((x_110 Heap_0) (x_111 list_1))
	(diseqlist_1 nil_2 (cons_1 x_110 x_111))))
(assert (forall ((x_112 Heap_0) (x_113 list_1))
	(diseqlist_1 (cons_1 x_112 x_113) nil_2)))
(assert (forall ((x_114 Heap_0) (x_115 list_1) (x_116 Heap_0) (x_117 list_1))
	(=> (diseqHeap_0 x_114 x_116)
	    (diseqlist_1 (cons_1 x_114 x_115) (cons_1 x_116 x_117)))))
(assert (forall ((x_114 Heap_0) (x_115 list_1) (x_116 Heap_0) (x_117 list_1))
	(=> (diseqlist_1 x_115 x_117)
	    (diseqlist_1 (cons_1 x_114 x_115) (cons_1 x_116 x_117)))))
(declare-fun toHeap_0 (list_1 list_0) Bool)
(assert (forall ((x_17 list_1) (y_0 Nat_0) (z_0 list_0))
	(=> (toHeap_0 x_17 z_0)
	    (toHeap_0 (cons_1 (Node_0 Nil_1 y_0 Nil_1) x_17) (cons_0 y_0 z_0)))))
(assert (toHeap_0 nil_2 nil_0))
(declare-fun leq_0 (Bool_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_19 Bool_0) (x_2 Nat_0) (z_1 Nat_0))
	(=> (leq_0 x_19 z_1 x_2)
	    (leq_0 x_19 (succ_0 z_1) (succ_0 x_2)))))
(assert (forall ((z_1 Nat_0))
	(leq_0 false_0 (succ_0 z_1) zero_0)))
(assert (forall ((y_1 Nat_0))
	(leq_0 true_0 zero_0 y_1)))
(declare-fun ordered_0 (Bool_0 list_0) Bool)
(assert (forall ((x_23 Bool_0) (x_24 Bool_0) (x_25 Bool_0) (y_3 Nat_0) (xs_0 list_0) (y_2 Nat_0))
	(=>	(and (leq_0 x_24 y_2 y_3)
			(ordered_0 x_25 (cons_0 y_3 xs_0))
			(and_0 x_23 x_24 x_25))
		(ordered_0 x_23 (cons_0 y_2 (cons_0 y_3 xs_0))))))
(assert (forall ((y_2 Nat_0))
	(ordered_0 true_0 (cons_0 y_2 nil_0))))
(assert (ordered_0 true_0 nil_0))
(declare-fun hmerge_0 (Heap_0 Heap_0 Heap_0) Bool)
(assert (forall ((x_28 Heap_0))
	(hmerge_0 x_28 Nil_1 x_28)))
(assert (forall ((z_3 Heap_0) (x_5 Nat_0) (x_6 Heap_0))
	(hmerge_0 (Node_0 z_3 x_5 x_6) (Node_0 z_3 x_5 x_6) Nil_1)))
(assert (forall ((x_32 Heap_0) (x_7 Heap_0) (x_8 Nat_0) (x_9 Heap_0) (z_3 Heap_0) (x_5 Nat_0) (x_6 Heap_0))
	(=>	(and (hmerge_0 x_32 x_6 (Node_0 x_7 x_8 x_9))
			(leq_0 true_0 x_5 x_8))
		(hmerge_0 (Node_0 x_32 x_5 z_3) (Node_0 z_3 x_5 x_6) (Node_0 x_7 x_8 x_9)))))
(assert (forall ((x_35 Heap_0) (x_33 Bool_0) (x_7 Heap_0) (x_8 Nat_0) (x_9 Heap_0) (z_3 Heap_0) (x_5 Nat_0) (x_6 Heap_0))
	(=>	(and (diseqBool_0 x_33 true_0)
			(hmerge_0 x_35 (Node_0 z_3 x_5 x_6) x_9)
			(leq_0 x_33 x_5 x_8))
		(hmerge_0 (Node_0 x_35 x_8 x_7) (Node_0 z_3 x_5 x_6) (Node_0 x_7 x_8 x_9)))))
(declare-fun hpairwise_0 (list_1 list_1) Bool)
(assert (forall ((x_37 Heap_0) (x_38 list_1) (r_0 Heap_0) (qs_0 list_1) (q_0 Heap_0))
	(=>	(and (hmerge_0 x_37 q_0 r_0)
			(hpairwise_0 x_38 qs_0))
		(hpairwise_0 (cons_1 x_37 x_38) (cons_1 q_0 (cons_1 r_0 qs_0))))))
(assert (forall ((q_0 Heap_0))
	(hpairwise_0 (cons_1 q_0 nil_2) (cons_1 q_0 nil_2))))
(assert (hpairwise_0 nil_2 nil_2))
(declare-fun hmerging_0 (Heap_0 list_1) Bool)
(assert (forall ((x_41 Heap_0) (x_42 list_1) (z_4 Heap_0) (x_12 list_1) (q_1 Heap_0))
	(=>	(and (hpairwise_0 x_42 (cons_1 q_1 (cons_1 z_4 x_12)))
			(hmerging_0 x_41 x_42))
		(hmerging_0 x_41 (cons_1 q_1 (cons_1 z_4 x_12))))))
(assert (forall ((q_1 Heap_0))
	(hmerging_0 q_1 (cons_1 q_1 nil_2))))
(assert (hmerging_0 Nil_1 nil_2))
(declare-fun toHeap_1 (Heap_0 list_0) Bool)
(assert (forall ((x_46 Heap_0) (x_47 list_1) (x_13 list_0))
	(=>	(and (toHeap_0 x_47 x_13)
			(hmerging_0 x_46 x_47))
		(toHeap_1 x_46 x_13))))
(declare-fun toList_0 (list_0 Heap_0) Bool)
(assert (toList_0 nil_0 Nil_1))
(assert (forall ((x_51 Heap_0) (x_52 list_0) (q_2 Heap_0) (y_7 Nat_0) (r_1 Heap_0))
	(=>	(and (hmerge_0 x_51 q_2 r_1)
			(toList_0 x_52 x_51))
		(toList_0 (cons_0 y_7 x_52) (Node_0 q_2 y_7 r_1)))))
(declare-fun hsort_0 (list_0 list_0) Bool)
(assert (forall ((x_53 list_0) (x_54 Heap_0) (x_15 list_0))
	(=>	(and (toHeap_1 x_54 x_15)
			(toList_0 x_53 x_54))
		(hsort_0 x_53 x_15))))
(assert (forall ((x_56 list_0) (x_57 Bool_0) (xs_1 list_0))
	(=>	(and (diseqBool_0 x_57 true_0)
			(hsort_0 x_56 xs_1)
			(ordered_0 x_57 x_56))
		false)))
(check-sat)
