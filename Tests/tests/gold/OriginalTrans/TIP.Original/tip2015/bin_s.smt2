(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_0 ) (Z_1 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_22 Nat_0))
	(unS_1 x_22 (Z_1 x_22))))
(assert (isZ_2 Z_0))
(assert (forall ((x_24 Nat_0))
	(isZ_3 (Z_1 x_24))))
(assert (forall ((x_25 Nat_0))
	(diseqNat_0 Z_0 (Z_1 x_25))))
(assert (forall ((x_26 Nat_0))
	(diseqNat_0 (Z_1 x_26) Z_0)))
(assert (forall ((x_27 Nat_0) (x_28 Nat_0))
	(=> (diseqNat_0 x_27 x_28)
	    (diseqNat_0 (Z_1 x_27) (Z_1 x_28)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_0 Nat_0))
	(add_0 y_0 Z_0 y_0)))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_0 Nat_0))
	(=> (add_0 r_0 x_16 y_0)
	    (add_0 (Z_1 r_0) (Z_1 x_16) y_0))))
(assert (forall ((y_0 Nat_0))
	(minus_0 Z_0 Z_0 y_0)))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_0 Nat_0))
	(=> (minus_0 r_0 x_16 y_0)
	    (minus_0 (Z_1 r_0) (Z_1 x_16) y_0))))
(assert (forall ((y_0 Nat_0))
	(le_0 Z_0 y_0)))
(assert (forall ((x_16 Nat_0) (y_0 Nat_0))
	(=> (le_0 x_16 y_0)
	    (le_0 (Z_1 x_16) (Z_1 y_0)))))
(assert (forall ((y_0 Nat_0))
	(ge_0 y_0 Z_0)))
(assert (forall ((x_16 Nat_0) (y_0 Nat_0))
	(=> (ge_0 x_16 y_0)
	    (ge_0 (Z_1 x_16) (Z_1 y_0)))))
(assert (forall ((y_0 Nat_0))
	(lt_0 Z_0 (Z_1 y_0))))
(assert (forall ((x_16 Nat_0) (y_0 Nat_0))
	(=> (lt_0 x_16 y_0)
	    (lt_0 (Z_1 x_16) (Z_1 y_0)))))
(assert (forall ((y_0 Nat_0))
	(gt_0 (Z_1 y_0) Z_0)))
(assert (forall ((x_16 Nat_0) (y_0 Nat_0))
	(=> (gt_0 x_16 y_0)
	    (gt_0 (Z_1 x_16) (Z_1 y_0)))))
(assert (forall ((y_0 Nat_0))
	(mult_0 Z_0 Z_0 y_0)))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_0 Nat_0) (z_2 Nat_0))
	(=>	(and (mult_0 r_0 x_16 y_0)
			(add_0 z_2 r_0 y_0))
		(mult_0 z_2 (Z_1 x_16) y_0))))
(assert (forall ((x_16 Nat_0) (y_0 Nat_0))
	(=> (lt_0 x_16 y_0)
	    (div_0 Z_0 x_16 y_0))))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_0 Nat_0) (z_2 Nat_0))
	(=>	(and (ge_0 x_16 y_0)
			(minus_0 z_2 x_16 y_0)
			(div_0 r_0 z_2 y_0))
		(div_0 (Z_1 r_0) x_16 y_0))))
(assert (forall ((x_16 Nat_0) (y_0 Nat_0))
	(=> (lt_0 x_16 y_0)
	    (mod_0 x_16 x_16 y_0))))
(assert (forall ((r_0 Nat_0) (x_16 Nat_0) (y_0 Nat_0) (z_2 Nat_0))
	(=>	(and (ge_0 x_16 y_0)
			(minus_0 z_2 x_16 y_0)
			(mod_0 r_0 z_2 y_0))
		(mod_0 r_0 x_16 y_0))))
(declare-datatypes ((Bin_0 0)) (((One_0 ) (ZeroAnd_0 (projZeroAnd_0 Bin_0)) (OneAnd_0 (projOneAnd_0 Bin_0)))))
(declare-fun diseqBin_0 (Bin_0 Bin_0) Bool)
(declare-fun projZeroAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun projOneAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun isOne_0 (Bin_0) Bool)
(declare-fun isZeroAnd_0 (Bin_0) Bool)
(declare-fun isOneAnd_0 (Bin_0) Bool)
(assert (forall ((x_30 Bin_0))
	(projZeroAnd_1 x_30 (ZeroAnd_0 x_30))))
(assert (forall ((x_32 Bin_0))
	(projOneAnd_1 x_32 (OneAnd_0 x_32))))
(assert (isOne_0 One_0))
(assert (forall ((x_34 Bin_0))
	(isZeroAnd_0 (ZeroAnd_0 x_34))))
(assert (forall ((x_35 Bin_0))
	(isOneAnd_0 (OneAnd_0 x_35))))
(assert (forall ((x_36 Bin_0))
	(diseqBin_0 One_0 (ZeroAnd_0 x_36))))
(assert (forall ((x_37 Bin_0))
	(diseqBin_0 One_0 (OneAnd_0 x_37))))
(assert (forall ((x_38 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_38) One_0)))
(assert (forall ((x_39 Bin_0))
	(diseqBin_0 (OneAnd_0 x_39) One_0)))
(assert (forall ((x_40 Bin_0) (x_41 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_40) (OneAnd_0 x_41))))
(assert (forall ((x_42 Bin_0) (x_43 Bin_0))
	(diseqBin_0 (OneAnd_0 x_42) (ZeroAnd_0 x_43))))
(assert (forall ((x_44 Bin_0) (x_45 Bin_0))
	(=> (diseqBin_0 x_44 x_45)
	    (diseqBin_0 (ZeroAnd_0 x_44) (ZeroAnd_0 x_45)))))
(assert (forall ((x_46 Bin_0) (x_47 Bin_0))
	(=> (diseqBin_0 x_46 x_47)
	    (diseqBin_0 (OneAnd_0 x_46) (OneAnd_0 x_47)))))
(declare-fun toNat_0 (Nat_0 Bin_0) Bool)
(assert (forall ((x_17 Nat_0) (x_18 Nat_0) (x_3 Nat_0) (x_4 Nat_0) (ys_0 Bin_0))
	(=>	(and (toNat_0 x_3 ys_0)
			(toNat_0 x_4 ys_0)
			(add_0 x_17 (Z_1 Z_0) x_3)
			(add_0 x_18 x_17 x_4))
		(toNat_0 x_18 (OneAnd_0 ys_0)))))
(assert (forall ((x_19 Nat_0) (x_6 Nat_0) (x_7 Nat_0) (xs_0 Bin_0))
	(=>	(and (toNat_0 x_6 xs_0)
			(toNat_0 x_7 xs_0)
			(add_0 x_19 x_6 x_7))
		(toNat_0 x_19 (ZeroAnd_0 xs_0)))))
(assert (toNat_0 (Z_1 Z_0) One_0))
(declare-fun s_0 (Bin_0 Bin_0) Bool)
(assert (forall ((x_10 Bin_0) (ys_1 Bin_0))
	(=> (s_0 x_10 ys_1)
	    (s_0 (ZeroAnd_0 x_10) (OneAnd_0 ys_1)))))
(assert (forall ((xs_1 Bin_0))
	(s_0 (OneAnd_0 xs_1) (ZeroAnd_0 xs_1))))
(assert (s_0 (ZeroAnd_0 One_0) One_0))
(assert (forall ((x_20 Nat_0) (x_13 Bin_0) (x_14 Nat_0) (x_15 Nat_0) (n_0 Bin_0))
	(=>	(and (diseqNat_0 x_14 x_20)
			(s_0 x_13 n_0)
			(toNat_0 x_14 x_13)
			(toNat_0 x_15 n_0)
			(add_0 x_20 (Z_1 Z_0) x_15))
		false)))
(check-sat)
