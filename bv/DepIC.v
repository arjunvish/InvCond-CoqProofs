From BV Require Import BVList.
Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

From Hammer Require Import Hammer Reconstr.

 Include RAW2BITVECTOR(RAWBITVECTOR_LIST).

(*------------------------------Addition------------------------------*)
Theorem bvadd_dep: forall (n : N), forall (s t : bitvector n),
    iff 
    (exists (x : bitvector n), bv_eq (bv_add x s) t = true)
    True.
Proof. intros n s t.
        split; intro A.
        - easy.
        - exists (bv_subt' t s).
          now rewrite bv_add_subst_opp.
Qed.

(* (exists x, (s >>a s) <u t) => ((s <u t \/ s >=s 0) /\ t != 0) *)
Theorem bvashr_ult2_ltr : forall (n : N), forall (s t : bitvector n),
    (exists (x : bitvector n), (bv_ult (bv_ashr_a s x) t = true)) ->
    (((bv_ult s t = true) \/ (bv_slt s (zeros n)) = false) /\ 
    (bv_eq t (zeros n)) = false).
Proof. intros. split.
        destruct H as (x, H2).
        destruct s as (s, H).
        destruct t as (t, H0).
        destruct x as (x, H1).
        unfold bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.
        rewrite RAWBITVECTOR_LIST.bv_ult_nat in *.
        unfold RAWBITVECTOR_LIST.bv_ashr_a in *.
        rewrite H, H1, N.eqb_refl in H2.
        unfold RAWBITVECTOR_LIST.ashr_aux_a, 
        RAWBITVECTOR_LIST.list2nat_be_a, RAWBITVECTOR_LIST.ashr_n_bits_a in *.
        case_eq ((N.to_nat (RAWBITVECTOR_LIST.list2N x) <? length s)%nat); intros. 
        - rewrite H3 in H2.
          case_eq (eqb (last s false) false); intros.
          + rewrite H4 in H2.
            assert ((last s false) = false).
            { destruct ((last s false)); intros; cbn in H4; easy. }
            unfold RAWBITVECTOR_LIST.zeros. 
            specialize (RAWBITVECTOR_LIST.last_mk_list_false (N.to_nat (RAWBITVECTOR_LIST.size s))); intros.
            rewrite RAWBITVECTOR_LIST.bv_slt_ult_last_eq with (d := false). (*[ | now rewrite H5, H6].*)
            rewrite RAWBITVECTOR_LIST.bv_ult_nat in *.
            right.
            unfold RAWBITVECTOR_LIST.bv2nat_a, RAWBITVECTOR_LIST.list2nat_be_a, RAWBITVECTOR_LIST.size
            in *. rewrite <- H.
            now rewrite Nat2N.id, RAWBITVECTOR_LIST.list_lt_false.
	          Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl,  
              @RAWBITVECTOR_LIST.length_mk_list_false, 
              @Coq.NArith.Nnat.N2Nat.id) (@RAWBITVECTOR_LIST.size).
            Reconstr.reasy Reconstr.Empty Reconstr.Empty.
          + rewrite H4 in H2.
            unfold RAWBITVECTOR_LIST.bv2nat_a, RAWBITVECTOR_LIST.list2nat_be_a, 
             RAWBITVECTOR_LIST.zeros, RAWBITVECTOR_LIST.size in *.
            left.
            destruct (RAWBITVECTOR_LIST.n_cases_all (N.to_nat (RAWBITVECTOR_LIST.list2N x))).
            * rewrite H5 in *.
              rewrite RAWBITVECTOR_LIST.skip0 in H2.
              assert (RAWBITVECTOR_LIST.mk_list_true 0 = nil) by easy.
              now rewrite H6, app_nil_r in H2.
            * destruct (RAWBITVECTOR_LIST.list_cases_all_true s).
              ** rewrite H6 in H2.
                 rewrite RAWBITVECTOR_LIST.skipn_nm in H2; [ | easy].
                 now rewrite H6.
              ** specialize (@RAWBITVECTOR_LIST.skipn_gt (N.to_nat (RAWBITVECTOR_LIST.list2N x)) s H5 H3 H6); intros.
                 apply Nat.ltb_lt.
                 apply Nat.ltb_lt in H2.
                 apply Nat.ltb_lt in H7.
                 lia.
        - rewrite H3 in H2.
          case_eq (eqb (last s false) false); intros.
          + rewrite H4 in H2.
            assert ((last s false) = false).
            { destruct ((last s false)); intros; cbn in H4; easy. }
            unfold zeros. 
            specialize (RAWBITVECTOR_LIST.last_mk_list_false (N.to_nat (RAWBITVECTOR_LIST.size s))); intros.
            rewrite RAWBITVECTOR_LIST.bv_slt_ult_last_eq with (d := false).
            rewrite RAWBITVECTOR_LIST.bv_ult_nat in *.
            right. unfold RAWBITVECTOR_LIST.bv2nat_a, RAWBITVECTOR_LIST.list2nat_be_a,
            RAWBITVECTOR_LIST.zeros, 
            RAWBITVECTOR_LIST.size in *.
            rewrite <- H.
            now rewrite Nat2N.id, RAWBITVECTOR_LIST.list_lt_false.
            Reconstr.reasy (@RAWBITVECTOR_LIST.zeros_size, @Coq.NArith.BinNat.N.eqb_refl) Reconstr.Empty.
            	Reconstr.reasy Reconstr.Empty (@RAWBITVECTOR_LIST.zeros).
          + rewrite H4 in H2. unfold RAWBITVECTOR_LIST.bv_slt, RAWBITVECTOR_LIST.slt_list.
            unfold RAWBITVECTOR_LIST.bv2nat_a, RAWBITVECTOR_LIST.list2nat_be_a, RAWBITVECTOR_LIST.size in *.
            left.
            destruct (RAWBITVECTOR_LIST.list_cases_all_true s).
            * now rewrite H5.
            * specialize (@RAWBITVECTOR_LIST.pow_ltb s H5); intros.
              apply Nat.ltb_lt.
              apply Nat.ltb_lt in H2.
              apply Nat.ltb_lt in H6. 
              lia.
        - unfold RAWBITVECTOR_LIST.bv_ashr_a. 
          rewrite H, H1, N.eqb_refl.
          specialize (@RAWBITVECTOR_LIST.length_ashr_aux_a s x (N.to_nat n)); intros.
          unfold RAWBITVECTOR_LIST.size in *.
          rewrite <- H3.
          Reconstr.reasy (@NBoolEqualityFacts.eqb_refl, @Coq.NArith.Nnat.N2Nat.id) Reconstr.Empty.
	        Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@RAWBITVECTOR_LIST.bitvector).
	        Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@RAWBITVECTOR_LIST.bitvector).
        - Reconstr.reasy (@Coq.NArith.BinNat.N.eqb_refl) Reconstr.Empty.
        - destruct H as (x, H2).
          destruct s as (s, H).
          destruct t as (t, H0).
          destruct x as (x, H1).
          unfold bv_eq, bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.

          unfold RAWBITVECTOR_LIST.bv_eq. rewrite H0. 
          unfold RAWBITVECTOR_LIST.zeros, RAWBITVECTOR_LIST.size.
          rewrite RAWBITVECTOR_LIST.length_mk_list_false, N2Nat.id, N.eqb_refl.
          unfold RAWBITVECTOR_LIST.bits.
          rewrite RAWBITVECTOR_LIST.bv_ult_nat in *.
          unfold RAWBITVECTOR_LIST.bv_ashr_a in *.
          rewrite H, H1, N.eqb_refl in H2.
          specialize (@RAWBITVECTOR_LIST.bv2nat_gt0 t (RAWBITVECTOR_LIST.bv2nat_a (RAWBITVECTOR_LIST.ashr_aux_a s x)) H2); intros.
          rewrite <- H0. unfold RAWBITVECTOR_LIST.size.
          rewrite Nat2N.id.
          now apply RAWBITVECTOR_LIST.List_neq2 in H3.
          unfold RAWBITVECTOR_LIST.bv_ashr_a.
          rewrite H, H1, N.eqb_refl. 
          specialize (@RAWBITVECTOR_LIST.length_ashr_aux_a s x (N.to_nat n)); intros.
          unfold RAWBITVECTOR_LIST.size in *.
          rewrite <- H3.
          Reconstr.reasy (@NBoolEqualityFacts.eqb_refl, @Coq.NArith.Nnat.N2Nat.id) Reconstr.Empty.
          lia. lia.
Qed.


