(set-logic HORN)
(declare-datatypes ((Nat_1 0)) (((Z_2 ) (Z_3 (unS_0 Nat_1)))))
(declare-fun diseqNat_1 (Nat_1 Nat_1) Bool)
(declare-fun unS_1 (Nat_1 Nat_1) Bool)
(declare-fun isZ_3 (Nat_1) Bool)
(declare-fun isZ_4 (Nat_1) Bool)
(assert (forall ((x_50 Nat_1))
	(unS_1 x_50 (Z_3 x_50))))
(assert (isZ_3 Z_2))
(assert (forall ((x_52 Nat_1))
	(isZ_4 (Z_3 x_52))))
(assert (forall ((x_53 Nat_1))
	(diseqNat_1 Z_2 (Z_3 x_53))))
(assert (forall ((x_54 Nat_1))
	(diseqNat_1 (Z_3 x_54) Z_2)))
(assert (forall ((x_55 Nat_1) (x_56 Nat_1))
	(=> (diseqNat_1 x_55 x_56)
	    (diseqNat_1 (Z_3 x_55) (Z_3 x_56)))))
(declare-fun add_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun minus_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun le_0 (Nat_1 Nat_1) Bool)
(declare-fun ge_0 (Nat_1 Nat_1) Bool)
(declare-fun lt_0 (Nat_1 Nat_1) Bool)
(declare-fun gt_0 (Nat_1 Nat_1) Bool)
(declare-fun mult_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun div_0 (Nat_1 Nat_1 Nat_1) Bool)
(declare-fun mod_0 (Nat_1 Nat_1 Nat_1) Bool)
(assert (forall ((y_3 Nat_1))
	(add_0 y_3 Z_2 y_3)))
(assert (forall ((r_2 Nat_1) (x_20 Nat_1) (y_3 Nat_1))
	(=> (add_0 r_2 x_20 y_3)
	    (add_0 (Z_3 r_2) (Z_3 x_20) y_3))))
(assert (forall ((y_3 Nat_1))
	(minus_0 Z_2 Z_2 y_3)))
(assert (forall ((r_2 Nat_1) (x_20 Nat_1) (y_3 Nat_1))
	(=> (minus_0 r_2 x_20 y_3)
	    (minus_0 (Z_3 r_2) (Z_3 x_20) y_3))))
(assert (forall ((y_3 Nat_1))
	(le_0 Z_2 y_3)))
(assert (forall ((x_20 Nat_1) (y_3 Nat_1))
	(=> (le_0 x_20 y_3)
	    (le_0 (Z_3 x_20) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(ge_0 y_3 Z_2)))
(assert (forall ((x_20 Nat_1) (y_3 Nat_1))
	(=> (ge_0 x_20 y_3)
	    (ge_0 (Z_3 x_20) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(lt_0 Z_2 (Z_3 y_3))))
(assert (forall ((x_20 Nat_1) (y_3 Nat_1))
	(=> (lt_0 x_20 y_3)
	    (lt_0 (Z_3 x_20) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(gt_0 (Z_3 y_3) Z_2)))
(assert (forall ((x_20 Nat_1) (y_3 Nat_1))
	(=> (gt_0 x_20 y_3)
	    (gt_0 (Z_3 x_20) (Z_3 y_3)))))
(assert (forall ((y_3 Nat_1))
	(mult_0 Z_2 Z_2 y_3)))
(assert (forall ((r_2 Nat_1) (x_20 Nat_1) (y_3 Nat_1) (z_4 Nat_1))
	(=>	(and (mult_0 r_2 x_20 y_3)
			(add_0 z_4 r_2 y_3))
		(mult_0 z_4 (Z_3 x_20) y_3))))
(assert (forall ((x_20 Nat_1) (y_3 Nat_1))
	(=> (lt_0 x_20 y_3)
	    (div_0 Z_2 x_20 y_3))))
(assert (forall ((r_2 Nat_1) (x_20 Nat_1) (y_3 Nat_1) (z_4 Nat_1))
	(=>	(and (ge_0 x_20 y_3)
			(minus_0 z_4 x_20 y_3)
			(div_0 r_2 z_4 y_3))
		(div_0 (Z_3 r_2) x_20 y_3))))
(assert (forall ((x_20 Nat_1) (y_3 Nat_1))
	(=> (lt_0 x_20 y_3)
	    (mod_0 x_20 x_20 y_3))))
(assert (forall ((r_2 Nat_1) (x_20 Nat_1) (y_3 Nat_1) (z_4 Nat_1))
	(=>	(and (ge_0 x_20 y_3)
			(minus_0 z_4 x_20 y_3)
			(mod_0 r_2 z_4 y_3))
		(mod_0 r_2 x_20 y_3))))
(declare-datatypes ((Tree_0 0)) (((Leaf_0 ) (Node_0 (projNode_0 Tree_0) (projNode_1 Nat_1) (projNode_2 Tree_0)))))
(declare-fun diseqTree_0 (Tree_0 Tree_0) Bool)
(declare-fun projNode_3 (Tree_0 Tree_0) Bool)
(declare-fun projNode_4 (Nat_1 Tree_0) Bool)
(declare-fun projNode_5 (Tree_0 Tree_0) Bool)
(declare-fun isLeaf_0 (Tree_0) Bool)
(declare-fun isNode_0 (Tree_0) Bool)
(assert (forall ((x_22 Tree_0) (x_23 Nat_1) (x_24 Tree_0))
	(projNode_3 x_22 (Node_0 x_22 x_23 x_24))))
(assert (forall ((x_22 Tree_0) (x_23 Nat_1) (x_24 Tree_0))
	(projNode_4 x_23 (Node_0 x_22 x_23 x_24))))
(assert (forall ((x_22 Tree_0) (x_23 Nat_1) (x_24 Tree_0))
	(projNode_5 x_24 (Node_0 x_22 x_23 x_24))))
(assert (isLeaf_0 Leaf_0))
(assert (forall ((x_26 Tree_0) (x_27 Nat_1) (x_28 Tree_0))
	(isNode_0 (Node_0 x_26 x_27 x_28))))
(assert (forall ((x_29 Tree_0) (x_30 Nat_1) (x_31 Tree_0))
	(diseqTree_0 Leaf_0 (Node_0 x_29 x_30 x_31))))
(assert (forall ((x_32 Tree_0) (x_33 Nat_1) (x_34 Tree_0))
	(diseqTree_0 (Node_0 x_32 x_33 x_34) Leaf_0)))
(assert (forall ((x_35 Tree_0) (x_36 Nat_1) (x_37 Tree_0) (x_38 Tree_0) (x_39 Nat_1) (x_40 Tree_0))
	(=> (diseqTree_0 x_35 x_38)
	    (diseqTree_0 (Node_0 x_35 x_36 x_37) (Node_0 x_38 x_39 x_40)))))
(assert (forall ((x_35 Tree_0) (x_36 Nat_1) (x_37 Tree_0) (x_38 Tree_0) (x_39 Nat_1) (x_40 Tree_0))
	(=> (diseqNat_1 x_36 x_39)
	    (diseqTree_0 (Node_0 x_35 x_36 x_37) (Node_0 x_38 x_39 x_40)))))
(assert (forall ((x_35 Tree_0) (x_36 Nat_1) (x_37 Tree_0) (x_38 Tree_0) (x_39 Nat_1) (x_40 Tree_0))
	(=> (diseqTree_0 x_37 x_40)
	    (diseqTree_0 (Node_0 x_35 x_36 x_37) (Node_0 x_38 x_39 x_40)))))
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (S_0 (projS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun projS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isS_0 (Nat_0) Bool)
(assert (forall ((x_42 Nat_0))
	(projS_1 x_42 (S_0 x_42))))
(assert (isZ_2 Z_0))
(assert (forall ((x_44 Nat_0))
	(isS_0 (S_0 x_44))))
(assert (forall ((x_45 Nat_0))
	(diseqNat_0 Z_0 (S_0 x_45))))
(assert (forall ((x_46 Nat_0))
	(diseqNat_0 (S_0 x_46) Z_0)))
(assert (forall ((x_47 Nat_0) (x_48 Nat_0))
	(=> (diseqNat_0 x_47 x_48)
	    (diseqNat_0 (S_0 x_47) (S_0 x_48)))))
(declare-fun mirror_0 (Tree_0 Tree_0) Bool)
(assert (forall ((x_5 Tree_0) (x_6 Tree_0) (l_0 Tree_0) (y_0 Nat_1) (r_0 Tree_0))
	(=>	(and (mirror_0 x_5 r_0)
			(mirror_0 x_6 l_0))
		(mirror_0 (Node_0 x_5 y_0 x_6) (Node_0 l_0 y_0 r_0)))))
(assert (mirror_0 Leaf_0 Leaf_0))
(declare-fun max_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((x_9 Nat_0) (x_2 Nat_0) (z_1 Nat_0))
	(=> (max_0 x_9 z_1 x_2)
	    (max_0 (S_0 x_9) (S_0 z_1) (S_0 x_2)))))
(assert (forall ((z_1 Nat_0))
	(max_0 (S_0 z_1) (S_0 z_1) Z_0)))
(assert (forall ((x_11 Nat_0))
	(max_0 x_11 Z_0 x_11)))
(declare-fun height_0 (Nat_0 Tree_0) Bool)
(assert (forall ((x_13 Nat_0) (x_14 Nat_0) (x_15 Nat_0) (l_1 Tree_0) (y_2 Nat_1) (r_1 Tree_0))
	(=>	(and (height_0 x_13 l_1)
			(height_0 x_14 r_1)
			(max_0 x_15 x_13 x_14))
		(height_0 (S_0 x_15) (Node_0 l_1 y_2 r_1)))))
(assert (height_0 Z_0 Leaf_0))
(assert (forall ((x_17 Tree_0) (x_18 Nat_0) (x_19 Nat_0) (a_0 Tree_0))
	(=>	(and (diseqNat_0 x_18 x_19)
			(mirror_0 x_17 a_0)
			(height_0 x_18 x_17)
			(height_0 x_19 a_0))
		false)))
(check-sat)
