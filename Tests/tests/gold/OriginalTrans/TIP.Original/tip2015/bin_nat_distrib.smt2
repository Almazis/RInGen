(set-logic HORN)
(declare-datatypes ((Bin_0 0)) (((One_0 ) (ZeroAnd_0 (projZeroAnd_0 Bin_0)) (OneAnd_0 (projOneAnd_0 Bin_0)))))
(declare-fun diseqBin_0 (Bin_0 Bin_0) Bool)
(declare-fun projZeroAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun projOneAnd_1 (Bin_0 Bin_0) Bool)
(declare-fun isOne_0 (Bin_0) Bool)
(declare-fun isZeroAnd_0 (Bin_0) Bool)
(declare-fun isOneAnd_0 (Bin_0) Bool)
(assert (forall ((x_37 Bin_0))
	(projZeroAnd_1 x_37 (ZeroAnd_0 x_37))))
(assert (forall ((x_39 Bin_0))
	(projOneAnd_1 x_39 (OneAnd_0 x_39))))
(assert (isOne_0 One_0))
(assert (forall ((x_41 Bin_0))
	(isZeroAnd_0 (ZeroAnd_0 x_41))))
(assert (forall ((x_42 Bin_0))
	(isOneAnd_0 (OneAnd_0 x_42))))
(assert (forall ((x_43 Bin_0))
	(diseqBin_0 One_0 (ZeroAnd_0 x_43))))
(assert (forall ((x_44 Bin_0))
	(diseqBin_0 One_0 (OneAnd_0 x_44))))
(assert (forall ((x_45 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_45) One_0)))
(assert (forall ((x_46 Bin_0))
	(diseqBin_0 (OneAnd_0 x_46) One_0)))
(assert (forall ((x_47 Bin_0) (x_48 Bin_0))
	(diseqBin_0 (ZeroAnd_0 x_47) (OneAnd_0 x_48))))
(assert (forall ((x_49 Bin_0) (x_50 Bin_0))
	(diseqBin_0 (OneAnd_0 x_49) (ZeroAnd_0 x_50))))
(assert (forall ((x_51 Bin_0) (x_52 Bin_0))
	(=> (diseqBin_0 x_51 x_52)
	    (diseqBin_0 (ZeroAnd_0 x_51) (ZeroAnd_0 x_52)))))
(assert (forall ((x_53 Bin_0) (x_54 Bin_0))
	(=> (diseqBin_0 x_53 x_54)
	    (diseqBin_0 (OneAnd_0 x_53) (OneAnd_0 x_54)))))
(declare-fun s_0 (Bin_0 Bin_0) Bool)
(assert (forall ((x_6 Bin_0) (ys_0 Bin_0))
	(=> (s_0 x_6 ys_0)
	    (s_0 (ZeroAnd_0 x_6) (OneAnd_0 ys_0)))))
(assert (forall ((xs_0 Bin_0))
	(s_0 (OneAnd_0 xs_0) (ZeroAnd_0 xs_0))))
(assert (s_0 (ZeroAnd_0 One_0) One_0))
(declare-fun plus_0 (Bin_0 Bin_0 Bin_0) Bool)
(assert (forall ((x_10 Bin_0) (x_11 Bin_0) (ys_2 Bin_0) (x_2 Bin_0))
	(=>	(and (plus_0 x_10 x_2 ys_2)
			(s_0 x_11 x_10))
		(plus_0 (ZeroAnd_0 x_11) (OneAnd_0 x_2) (OneAnd_0 ys_2)))))
(assert (forall ((x_13 Bin_0) (zs_0 Bin_0) (x_2 Bin_0))
	(=> (plus_0 x_13 x_2 zs_0)
	    (plus_0 (OneAnd_0 x_13) (OneAnd_0 x_2) (ZeroAnd_0 zs_0)))))
(assert (forall ((x_14 Bin_0) (x_2 Bin_0))
	(=> (s_0 x_14 (OneAnd_0 x_2))
	    (plus_0 x_14 (OneAnd_0 x_2) One_0))))
(assert (forall ((x_17 Bin_0) (xs_1 Bin_0) (z_0 Bin_0))
	(=> (plus_0 x_17 z_0 xs_1)
	    (plus_0 (OneAnd_0 x_17) (ZeroAnd_0 z_0) (OneAnd_0 xs_1)))))
(assert (forall ((x_19 Bin_0) (ys_1 Bin_0) (z_0 Bin_0))
	(=> (plus_0 x_19 z_0 ys_1)
	    (plus_0 (ZeroAnd_0 x_19) (ZeroAnd_0 z_0) (ZeroAnd_0 ys_1)))))
(assert (forall ((x_20 Bin_0) (z_0 Bin_0))
	(=> (s_0 x_20 (ZeroAnd_0 z_0))
	    (plus_0 x_20 (ZeroAnd_0 z_0) One_0))))
(assert (forall ((x_22 Bin_0) (y_0 Bin_0))
	(=> (s_0 x_22 y_0)
	    (plus_0 x_22 One_0 y_0))))
(declare-fun times_0 (Bin_0 Bin_0 Bin_0) Bool)
(assert (forall ((x_24 Bin_0) (x_25 Bin_0) (xs_3 Bin_0) (y_1 Bin_0))
	(=>	(and (times_0 x_25 xs_3 y_1)
			(plus_0 x_24 (ZeroAnd_0 x_25) y_1))
		(times_0 x_24 (OneAnd_0 xs_3) y_1))))
(assert (forall ((x_28 Bin_0) (xs_2 Bin_0) (y_1 Bin_0))
	(=> (times_0 x_28 xs_2 y_1)
	    (times_0 (ZeroAnd_0 x_28) (ZeroAnd_0 xs_2) y_1))))
(assert (forall ((x_29 Bin_0))
	(times_0 x_29 One_0 x_29)))
(assert (forall ((x_30 Bin_0) (x_31 Bin_0) (x_32 Bin_0) (x_33 Bin_0) (x_34 Bin_0) (x_4 Bin_0) (y_2 Bin_0) (z_1 Bin_0))
	(=>	(and (diseqBin_0 x_31 x_34)
			(plus_0 x_30 y_2 z_1)
			(times_0 x_31 x_4 x_30)
			(times_0 x_32 x_4 y_2)
			(times_0 x_33 x_4 z_1)
			(plus_0 x_34 x_32 x_33))
		false)))
(check-sat)
