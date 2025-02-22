From BV Require Import BVList.

Import RAWBITVECTOR_LIST.

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

From Hammer Require Import Hammer Reconstr.

(* Start Practice:
 forall x : bitvector, size(x) >= 0*)

Theorem length_of_tail : forall (h : bool) (t : list bool), 
 length (h :: t) = S (length t).
  intros h t.
Proof. 
  induction t; reflexivity.
Qed.

Theorem non_empty_list_size : forall (h : bool) (t : list bool),
          N.to_nat (size (h :: t)) = S (N.to_nat (size t)).
Proof.
  intros h t. induction t as [| h' t' IHt].
    + reflexivity.
    + unfold size in *. rewrite -> length_of_tail.
      rewrite -> length_of_tail. rewrite -> Nat2N.id in *.
      rewrite -> Nat2N.id. reflexivity.
Qed.

Theorem succ_gt_pred : forall (n : nat), n >= 0 -> S n >= 0.
Proof.
  intros n. induction n as [| n' IHn].
  + unfold ge. intros H. apply le_0_n.
  + unfold ge. intros H. auto.
Qed.

Theorem bv_size_nonnegative : forall (x : bitvector), N.to_nat(size x) >= 0.
Proof.
  intros x. induction x.
  - auto.
  - rewrite -> non_empty_list_size. unfold size in *. 
    rewrite -> Nat2N.id in *. apply succ_gt_pred. apply IHx.
  Qed.

Lemma bvgez: forall a: bitvector, (bv2nat_a a = 0) \/ (bv2nat_a a > 0).
Proof. intro a.
       induction a.
       - cbn. left. easy.
       - case_eq a; intros.
         + right. unfold bv2nat_a, list2nat_be_a.
        	 Reconstr.rsimple (@Coq.Arith.Gt.gt_0_eq, @Coq.Arith.PeanoNat.Nat.add_0_l,
           @Coq.NArith.Nnat.N2Nat.inj_succ_double) 
          (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
           @BV.BVList.RAWBITVECTOR_LIST.list2N).
         + unfold bv2nat_a, list2nat_be_a. destruct IHa.
           * left. 
	           Reconstr.rblast (@Coq.NArith.Nnat.N2Nat.id, @BV.BVList.RAWBITVECTOR_LIST.list2N_N2List,
               @Coq.Init.Peano.O_S, @Coq.NArith.Nnat.Nat2N.id) 
              (@Coq.NArith.BinNatDef.N.of_nat, @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, 
               @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a, @Coq.NArith.BinNatDef.N.double, 
               @BV.BVList.RAWBITVECTOR_LIST.list2N).
           * right. cbn. 
	           Reconstr.rsimple (@Coq.NArith.Nnat.Nat2N.id, @Coq.PArith.Pnat.Pos2Nat.is_pos, 
              @Coq.Arith.PeanoNat.Nat.lt_irrefl, @BV.BVList.RAWBITVECTOR_LIST.list2N_N2List)
             (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a, @Coq.NArith.BinNatDef.N.to_nat, 
              @Coq.NArith.BinNatDef.N.of_nat,
              @Coq.Init.Peano.gt, @Coq.NArith.BinNatDef.N.double,
              @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a).
Qed.

(*
Lemma bv_non_neg : forall b : bitvector,
 (zeros (size b) = b) \/ (bv_ultP (zeros (size b)) b).
Proof.
  intro a. induction a.
  + left. easy.
  + case_eq a.
    - intros. unfold zeros in *. unfold size in *. 
      rewrite Nat2N.id in *. destruct IHa.
      * right. rewrite <- H0. admit.
      * right. admit.
    - intros. unfold zeros in *. unfold size in *. 
      rewrite Nat2N.id in *. destruct IHa.
      * left. assert (mk_list_false_succ : forall (h : bool) (t : list bool), 
                (mk_list_false (length (h :: t)) = 
                  (false :: (mk_list_false (length t))))). { admit. }
        rewrite (@mk_list_false_succ false a0). rewrite -> H0. easy.  
      * right. assert (mk_list_false_succ : forall (h : bool) (t : list bool), 
                (mk_list_false (length (h :: t)) = 
                  (false :: (mk_list_false (length t))))). { admit. }
        rewrite (@mk_list_false_succ false a0). unfold bv_ultP in *.
        case_eq ((size (false :: mk_list_false (length a0)) =? size (false :: a0))%N).
        { intros.   

Lemma mk_list_false_succ : forall (h : bool) (t : list bool), 
  (mk_list_false (length (h :: t)) = (false :: (mk_list_false (length t))).
Lemma bv_non_neg_aux : forall (h : bool) (t : list bool),
bv_ultP (zeros (length (h :: t))) (true :: t).
*)

 
Lemma bvdm: forall a b: bitvector, size a = size b ->
   (bv_not (bv_and a b)) = (bv_or (bv_not a) (bv_not b)).
Proof. intros. unfold bv_and, bv_or, bv_not.
       rewrite H, N.eqb_refl.
       unfold bits, size in *. 
       rewrite !map_length, H, N.eqb_refl.
       now rewrite not_list_and_or.
Qed.

(* End Practice *)


(*------------------------------Addition------------------------------*)
(* (exists x, x + s = t) <=> T *)
Theorem bvadd : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ((bv_add x s) = t))
    True.
Proof. 
    intros n s t Hs Ht.
    split; intro A.
    - easy.
    - exists (bv_subt' t s).
      split.
      + exact (bv_subt'_size Ht Hs).
      + now rewrite  (bv_add_subst_opp Ht Hs).
Qed.

(** BE: keep this; may be of use *)
Theorem bvadd_U: forall (n : N),
  forall (s t x: bitvector), (size s) = n /\ (size t) = n /\ (size x) = n ->
  (bv_add x s) = t <-> (x = (bv_subt' t s)).
Proof. intros n s t x (Hs, (Ht, Hx)).
  split; intro A.
  - rewrite <- A. symmetry. exact (@bv_subt'_add n x s Hx Hs).
  - rewrite A. exact (bv_add_subst_opp Ht Hs).
Qed.

(** BE: the same with bvadd *)
Theorem bvadd_e: forall (n : N),
  forall (s t : bitvector), (size s) = n /\ (size t) = n ->
  exists (x : bitvector), (size x) = n /\ (bv_add x s) = t.
Proof. intros n s t (Hs, Ht).
  exists (bv_subt' t s).
  split; [exact (bv_subt'_size Ht Hs) | exact (bv_add_subst_opp Ht Hs)].
Qed.
(*------------------------------------------------------------*)


(*------------------------------And------------------------------*)
(* (exists x, x & s = t) <=> t & s = t*)
Theorem bvand_eq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_and x s) = t) 
    ((bv_and t s) = t).
Proof. intros n s t Hs Ht.
       split; intro A.
       - destruct A as (x, (Hx, A)). rewrite <- A.
         now rewrite (@bv_and_comm n x s Hx Hs), (@bv_and_idem1 s x n Hs Hx).
       - exists t. split. 
         + apply Ht.
         + apply A.
Qed.

(* (exists x, x & s != t) <=> s != 0 or t != 0 *)
Theorem bvand_neq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_and x s) <> t) 
    (s <> zeros (size s) \/ t <> zeros (size t)).
Proof. intros n s t Hs Ht.
  split; intro A.
  + destruct A as (x, (Hx, A)).
    assert (H : (s = zeros (size s) /\ t = zeros (size t)) -> False). 
      { intros H'. destruct H' as (HS, HT).
        rewrite -> HS in A. rewrite -> HT in A.
        assert (Hsx : size s = size x).
        { rewrite Hx. rewrite Hs. auto. }
        rewrite -> Hsx in A.
        assert (Htx : size t = size x).
        { rewrite Hx. rewrite Ht. auto. }
        rewrite -> Htx in A. unfold zeros in A.
        unfold size in A. 
        rewrite Nat2N.id in A.
        assert (Hbits : forall b : bitvector, 
                length b = length (bits b)).
        { intro b. unfold bits. auto. }
        rewrite -> (@Hbits x) in A.
        rewrite (@bv_and_0_absorb x) in A. apply A. auto.
      }
  (* s = zeros (size s) /\ t = zeros (size t) -> False
    |= ~(s = zeros (size s) /\ t = zeros (size t))
    |= (s <> zeros (size s)) \/ (t <> zeros (size t))
  + s != 0 \/ t != 0 -> (exists x, x & s != t)
    not sure how to prove this direction *)
   Admitted.

        
(*
(* (exists x, x & s != t) <=> s != 0 or t != 0 *)
(** BE: statement incorrect? *)
Theorem bvand_neq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_and x s) <> t) 
    (s <> zeros (size s) \/ t <> zeros (size t)).
Proof. intros n s t Hs Ht.
       split; intro A. destruct A as (x, (Hx, A)).
       unfold not in *.
       left. intro HS. apply A.
       rewrite HS in A. unfold zeros in *.
       rewrite HS.
       specialize (@bv_and_0_absorb x); intro H.
       unfold bits in H. unfold size.
       rewrite Nat2N.id.
       assert (length s = length x) by admit.
       rewrite H0, H.
       unfold size in A.
       rewrite Nat2N.id, H0 in A.
Admitted.
*)

(* (exists x, x & s <u t) <=> (t != 0) *)
Theorem bvand_ult : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_and x s) t))
    (~(t = zeros (size t))).
Proof. 
  intros n s t Hs Ht.
  split; intro A.
  + destruct A as (x, (Hx, A)).
    assert (bv_non_neg : forall (b : bitvector), (zeros (size b)) = b
      \/ (bv_ultP (zeros (size b)) b)). 
      { admit. }
    assert (H : (zeros (size (bv_and x s))) = (bv_and x s) \/
      bv_ultP (zeros (size (bv_and x s))) (bv_and x s)).
      { apply bv_non_neg. }
    assert (trans_bv_ult : forall (x y z : bitvector), 
      (x = y) \/ (bv_ultP x y) -> (bv_ultP y z) 
      -> (bv_ultP x z)).
      { admit. }
    assert (H0 : bv_ultP (zeros (size t)) t).
      { specialize (@trans_bv_ult (zeros (size (bv_and x s))) 
          (bv_and x s) t H  A).
        rewrite (@bv_and_size n x s Hx Hs) in trans_bv_ult.
        rewrite <- Ht in trans_bv_ult. apply trans_bv_ult. }
    apply (@bv_ult_not_eqP (zeros (size t)) t) in H0.
    unfold not in *. intros. rewrite <- H1 in H0. now contradict H0.
  + exists (zeros n). split.
    - apply zeros_size.
    - assert (bv_and_0_absorb : forall (b : bitvector), 
        bv_and b (zeros (size b)) = (zeros (size b))).
        { admit. }
      rewrite (@bv_and_comm n (zeros n) s (@zeros_size n) Hs).
      rewrite <- Hs. rewrite (@bv_and_0_absorb s). 
      rewrite -> Hs. rewrite <- Ht. 
      assert (bv_neq_zero_bv_ultP : forall (b : bitvector), 
        b <> zeros (size b) -> bv_ultP (zeros (size b)) b).
        { admit. }
      apply bv_neq_zero_bv_ultP. apply A.
Admitted.

(* (exists x, x & s >u t) <=> (t <u s) *)
Theorem bvand_ugt : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_and x s) t))
    (bv_ultP t s).
Proof.
Admitted.
(*------------------------------------------------------------*)


(*------------------------------Or------------------------------*)
(* (exists x, x | s = t) <=> t & s = t *)
Theorem bvor_eq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_or x s) = t) 
    ((bv_or t s) = t).
Proof. intros n s t Hs Ht.
       split; intro A.
       - destruct A as (x, (Hx, A)). rewrite <- A.
         now rewrite (@bv_or_idem2 x s n Hx Hs).
       - exists t. split; easy.
Qed.

(* (exists x, x | s != t) <=> s != ~0 or t != ~0 *)
Theorem bvor_neq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~((bv_or x s) = t)) 
    (~(s = (bv_not (zeros (size s)))) 
      \/ 
      (~(t = (bv_not (zeros (size t)))))).
Proof.
Admitted.

(* (exists x, x | s <u t) <=> (s <u t) *)
Theorem bvor_ult : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_or x s) t))
    (bv_ultP s t).
Proof.
Admitted.

(* (exists x, x | s >u t) <=> (t <u ~0) *)
Theorem bvor_ugt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_or x s) t))
    (bv_ultP t (zeros (size t))).
Proof.
Admitted.
(*------------------------------------------------------------*)


(*------------------------------Logical right shift------------------------------*)
(* (exists x, x >> s = t) <=> (t << s) >> s = t *)
Theorem bvshr_eq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ bv_shr x s = t) 
    (bv_shr (bv_shl t s) s = t).
Proof. intros n s t Hs Ht.
       split; intro A.
       - destruct A as (x, (Hx, A)).
         rewrite <- A.
         rewrite !bv_shr_eq, bv_shl_eq.
         unfold bv_shl_a, bv_shr_a.
         rewrite Hx, Hs, N.eqb_refl.
         unfold size in *. rewrite length_shr_n_bits_a, Hx.
         rewrite N.eqb_refl.
         rewrite length_shl_n_bits_a, length_shr_n_bits_a, Hx.
         rewrite N.eqb_refl.
         now rewrite shr_n_shl_a.
       - exists (bv_shl_a t s). split.
         unfold size, bv_shl_a.
         rewrite Hs, Ht, N.eqb_refl.
         now rewrite length_shl_n_bits_a.
         rewrite bv_shr_eq.
         rewrite bv_shr_eq, bv_shl_eq in A.
         easy.
Qed.

(* (exists x, x >> s != t) <=> t != 0 or s <u Nat2BV (size(s)) *)
Theorem bvshr_neq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~(bv_shr x s = t))
    (~(t = zeros (size t)) 
      \/
      ((bv_ult s (nat2bv 
                  (N.to_nat (size s)) 
                  (N.to_nat(size s))))) 
      = 
      true).
Proof.
Admitted.

(** BE: did not get the restriction over i? *)
(* (exists x, s >> x = t) <=> [i=0...size(s)]OR(s >> i = t) *)
Theorem bvshr_eq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ bv_shr s x = t)
    (exists (i : nat), 
(*    i >= 0 /\ 
      i <= (N.to_nat (size s)) /\  *)
      ((bv_shr s (nat2bv i (N.to_nat (size s)))) = t)).
Proof. split; intros.
       - destruct H1 as (x, (H1, H2)).
         exists (bv2nat_a x).
         unfold bv2nat_a. 
         unfold nat2bv, list2nat_be_a.
         case_eq (N.to_nat (list2N x) =? 0); intros.
         rewrite bv_shr_eq in H2.
         unfold bv_shr_a, list2nat_be_a in H2. 
         apply Nat.eqb_eq in H3.
         rewrite H, H1, N.eqb_refl, H3 in H2.
         rewrite H3. cbn.
         rewrite bv_shr_eq. unfold bv_shr_a.
         unfold size.
         rewrite length_mk_list_false, N2Nat.id, Nat2N.id, N.eqb_refl.
         unfold list2nat_be_a. cbn.
         rewrite list2N_mk_list_false. easy.
         cbn. rewrite N2Nat.id.
         unfold shr_n_bits_a in H2. unfold size in *.
         rewrite H, <- H1.
         now rewrite Nat2N.id, N2List_list2N.
       - destruct H1 as (i, H1).
         exists (nat2bv i (N.to_nat (size s))). split.
         unfold size. rewrite Nat2N.id.
         now rewrite length_nat2bv.
         easy.
Qed.


(* (exists x, s >> x != t) <=> s != 0 or t != 0 *)
Theorem bvshr_neq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~(bv_shr s x = t))
    (~(s = zeros (size s))
      \/
     ~(t = zeros (size t))).
Proof.
Admitted.

(* (exists x, (x >> s) <u t) <=> (t != 0)*)
Theorem bvshr_ult : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ bv_ultP (bv_shr x s) t)
    (~(t = zeros (size t))).
Proof.
Admitted.

(* (exists x, (s >> x) <u t) <=> (t != 0) *)
Theorem bvshr_ult2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ bv_ultP (bv_shr s x) t)
    (~(t = zeros (size t))).
Proof.
Admitted.


(* (exists x, (x >> s) >u t) <= (t <u (~s >> s)) *)
Theorem bvshr_ugt_ltr : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (bv_ult t (bv_shr_a (bv_not s) s) = true) -> 
    (exists (x : bitvector), (size x = n) /\ bv_ugt (bv_shr_a x s) t = true).
Proof. intros.
       exists (bv_not s). split.
       Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.bv_not_size) Reconstr.Empty.
       apply bv_ult_bv_ugt.
       rewrite bv_ult_nat in *; 
       [ easy |
         unfold bv_shr_a, bv_not, size, bits;
         rewrite map_length, N.eqb_refl; 
         Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.not_list_length,
           @Coq.Arith.PeanoNat.Nat.eqb_eq, 
           @Coq.NArith.Nnat.Nat2N.id,
           @BV.BVList.RAWBITVECTOR_LIST.length_shr_n_bits_a) 
          (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
           @BV.BVList.RAWBITVECTOR_LIST.bv_not, 
           @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a,
           @BV.BVList.RAWBITVECTOR_LIST.size, 
           @BV.BVList.RAWBITVECTOR_LIST.bits) |
         unfold bv_shr_a, bv_not, size, bits;
         rewrite map_length, N.eqb_refl; 
         Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.not_list_length,
           @Coq.Arith.PeanoNat.Nat.eqb_eq, 
           @Coq.NArith.Nnat.Nat2N.id,
           @BV.BVList.RAWBITVECTOR_LIST.length_shr_n_bits_a) 
          (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
           @BV.BVList.RAWBITVECTOR_LIST.bv_not, 
           @BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a,
           @BV.BVList.RAWBITVECTOR_LIST.size, 
           @BV.BVList.RAWBITVECTOR_LIST.bits)].
Qed.

(* (exists x, (x >> s) >u t) <=> (t <u (~s >> s)) *)
Theorem bvshr_ugt : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ bv_ugtP (bv_shr x s) t)
    (bv_ultP t (bv_shr (bv_not s) s)).
Proof. 
  intros n s t Hs Ht. split. 
  + intros. destruct H as (x, (Hx, ugt_shr_t)). apply bv_ugtP_bv_ultP in ugt_shr_t.
    rewrite bv_shr_eq in *.
    assert (ule_shr_shrnot : forall (a b : bitvector), size a = size b ->
            lt (list2nat_be_a b) (length a) ->
            bv_uleP (bv_shr_a a b) (bv_shr_a (bv_not b) b)).
    { admit. }
    assert (lt_s_lenx : list2nat_be_a s < length x).
    { apply not_ge. unfold not. intros ge_s_lenx. unfold bv_shr_a in ugt_shr_t. 
      pose proof Hs as Hss. rewrite <- Hx in Hss. rewrite <- Hss in ugt_shr_t.
      assert (Hs_refl : (size s =? size s)%N = true). 
      { apply NBoolEqualityFacts.eqb_refl. }
      rewrite Hs_refl in ugt_shr_t. unfold shr_n_bits_a in ugt_shr_t. 
      assert (not_le_s_lenx : (list2nat_be_a s <? length x) = false).
      { rewrite Nat.ltb_ge. apply ge_s_lenx. } 
      rewrite not_le_s_lenx in ugt_shr_t. 
      pose proof not_bv_ultP_x_zero as not_lt. unfold zeros, size, not in not_lt.
      specialize (@not_lt t). rewrite (@Nat2N.id (length t)) in not_lt.
      pose proof Hx as lenxt. rewrite <- Ht in lenxt. unfold size in lenxt.
      apply Nat2N.inj in lenxt. rewrite lenxt in ugt_shr_t.
      specialize (@not_lt ugt_shr_t). apply not_lt. 
    }
    rewrite <- Hs in Hx. specialize (@ule_shr_shrnot x s Hx lt_s_lenx). 
    pose proof bv_ult_uleP_trans as trans.
    specialize (@trans t (bv_shr_a x s) (bv_shr_a (bv_not s) s) 
    ugt_shr_t ule_shr_shrnot). apply trans.
  + intros lt. exists (bv_not s). split.
    - apply (@bv_not_size n s Hs).
    - apply bv_ultP_bv_ugtP in lt. apply lt. 
Admitted.


(* (exists x, (s >> x) >u t) <=> (t <u s) *)
Theorem bvshr_ugt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ bv_ugtP (bv_shr s x) t)
    (bv_ultP t s).
Proof.
Admitted.
(*------------------------------------------------------------*)


(*------------------------------Logical left shift------------------------------*)
(* (exists x, x << s = t) <=> (t >> s) << s = t *)
Theorem bvshl_eq : forall (n : N), forall (s t : bitvector),
   (size s) = n -> (size t) = n -> iff
     (exists (x : bitvector), (size x = n) /\ bv_shl x s = t)
     (bv_shl (bv_shr t s) s = t).
Proof. intros n s t Hs Ht.
        split; intro A.
        - destruct A as (x, (Hx, A)).
          rewrite <- A.
          rewrite bv_shr_eq, !bv_shl_eq.
          unfold bv_shl_a, bv_shr_a.
          rewrite Hx, Hs, N.eqb_refl.
          unfold size in *. rewrite length_shl_n_bits_a, Hx.
          rewrite N.eqb_refl.
          rewrite length_shr_n_bits_a, length_shl_n_bits_a, Hx.
          rewrite N.eqb_refl.
          now rewrite shl_n_shr_a.
        - exists (bv_shr_a t s). split.
          unfold size, bv_shr_a.
         rewrite Hs, Ht, N.eqb_refl.
         now rewrite length_shr_n_bits_a.
         rewrite bv_shr_eq, bv_shl_eq in A.
         rewrite bv_shl_eq.
         easy.
Qed.


(* (exists x, x << s != t) => t != 0 or s <u size(s) *)
Theorem bvshl_neq_rtl: forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (exists (x : bitvector), (size x = n) /\ bv_eq (bv_shl_a x s) t = false) ->
    bv_eq t (zeros (size t)) = false \/ 
    bv_ult s (nat2bv (N.to_nat (size s)) (N.to_nat (size s))) = true.
Proof. intros.
        destruct H1 as (x, (H1, H2)).
        unfold nat2bv. rewrite N2Nat.id.
        unfold bv_shl_a, shl_n_bits_a, list2nat_be_a in *.
        rewrite bv_ult_nat in *.
        unfold bv2nat_a, list2nat_be_a.
        rewrite list2N_N2List_eq.
        rewrite H, H1, N.eqb_refl in H2.
        case_eq ( N.to_nat (list2N s) <? length x); intros.
        - right. rewrite H, <- H1. 
          unfold size. now rewrite Nat2N.id.
        (*- rewrite H3 in H2.
          destruct (list_cases_all_false t).
          + destruct (list_cases_all_false x).
            * rewrite H4, H5 in H2.
              Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id)
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                @BV.BVList.RAWBITVECTOR_LIST.size).
            * right. rewrite H, <- H1.
              unfold size. now rewrite Nat2N.id.
          + left. unfold zeros, size.
            rewrite Nat2N.id. 
            apply List_neq2 in H4.
            Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.bv_mk_eq) 
             (@BV.BVList.RAWBITVECTOR_LIST.bitvector).*)
        - rewrite H3 in H2. left.
          unfold zeros, size.
          rewrite Nat2N.id.
          unfold bv_eq in *.
          unfold size in *. rewrite length_mk_list_false in *.
          rewrite H1, H0, N.eqb_refl in H2.
          rewrite H0, N.eqb_refl.
          unfold bits in *.
          apply List_neq2.
          apply List_neq in H2.
          Reconstr.reasy (@BV.BVList.BITVECTOR_LIST.of_bits_size,
            @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
           (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
        - rewrite length_N2list.
          Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id, 
            @Coq.Arith.PeanoNat.Nat.eqb_eq) 
           (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
            @BV.BVList.RAWBITVECTOR_LIST.size).
Qed.

(* (exists x, x << s != t) <=> t != 0 or s <u size(s) *)
Theorem bvshl_neq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~(bv_shl x s = t))
    (~(t = zeros (size t))
     \/
     ((bv_ult s (nat2bv 
                  (N.to_nat (size s))
                  (N.to_nat (size s)))))
      =
      true).
Proof.
Admitted.

(* (exists x, s << x = t) <=> [i=0...size(s)]OR(s << i = t)  *)
Theorem bvshl_eq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_shl s x = t))
    (exists (i : nat), 
(*    (i >= 0) /\ 
      (i <= (N.to_nat (size s))) /\ *)
      ((bv_shl s (nat2bv i (N.to_nat (size s)))) = t)).
Proof. split; intros.
       - destruct H1 as (x, (H1, H2)).
         exists (bv2nat_a x).
         unfold bv2nat_a. 
         unfold nat2bv, list2nat_be_a.
         rewrite N2Nat.id. unfold size in *.
         rewrite H, <- H1, Nat2N.id. now rewrite N2List_list2N.
       - destruct H1 as (i, H1).
         exists (nat2bv i (N.to_nat (size s))). split.
         unfold size. rewrite Nat2N.id.
         now rewrite length_nat2bv.
         easy.
Qed.

(* (exists x, s << x != t) <=> s != 0 or or t != 0 *)
Theorem bvshl_neq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~(bv_shl s x = t))
    (~(s = zeros (size s)) \/ ~(t = zeros (size t))).
Proof.
Admitted.

(* (exists x, x << s <u t) <=> (t != 0) *)
Theorem bvshl_ult : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_shl x s) t))
    (~(t = zeros (size t))).
Proof.
Admitted.

(* (exists x, s << x <u t) <=> (t != 0) *)
Theorem bvshl_ult2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_shl s x) t))
    (~(t = zeros (size t))).
Proof.
Admitted.

(* (exists x, x << s >u t) <=> (t <u (~0 << s)) *)
Theorem bvshl_ugt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_shl x s) t))
    (bv_ultP t (bv_shl (bv_not (zeros (size s))) s)).
Proof.
  intros n s t Hs Ht.
  split. 
  + intros. destruct H as (x, (Hx, H1)).
    apply bv_ugtP_bv_ultP in H1. rewrite bv_shl_eq in *. 
    assert (forall (n : N) (x s : bitvector), size x = n 
            -> size s = n -> 
            bv_uleP (bv_shl_a x s) 
              (bv_shl_a (bv_not (zeros (size s))) s)).
    { apply bv_shl_a_1_leq. }
    assert (bv_ultP_eq_trans : forall b1 b2 b3 : bitvector, 
            bv_ultP b1 b2 -> bv_uleP b2 b3 -> 
            bv_ultP b1 b3).
    { apply bv_ult_uleP_trans. }
    specialize (@H n x s Hx Hs).
    specialize (@bv_ultP_eq_trans t (bv_shl_a x s) 
              (bv_shl_a (bv_not (zeros (size s))) s) H1 H).
    apply bv_ultP_eq_trans.
  + intro. exists (bv_not (zeros (size s))).
    split. 
    - apply bv_not_size. rewrite (zeros_size (size s)). 
      apply  Hs. 
    - apply bv_ultP_bv_ugtP. apply H.
Qed.

(* (exists x, (s << x) >u t) <=> 
   (exists i, 0 <= i < size(s), (s << i) >u t) *)
Theorem bvshl_ugt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_shl s x) t))
    (exists (i : nat), (i >= 0) /\ (i < N.to_nat (size s)) /\
      (bv_ugtP (bv_shl s (nat2bv i (N.to_nat (size t)))) t)).
Proof.
Admitted.
(*------------------------------------------------------------*)

(*------------------------------Arithmetic right shift------------------------------*)
(* (exists x, x >>a s = t) 
      <=> 
  (s <u size(s) => (t << s) >>a s = t) 
    and 
    (s >=u size(s) => (t = ~0 or t = 0)) *)
Theorem bvashr_eq : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ashr_a x s = t))
    (((bv_ult s (nat2bv (N.to_nat (size s)) (N.to_nat (size s)))  = true) 
      ->  bv_ashr_a (bv_shl t s) s = t)
                        /\
     ((bv_ult s (nat2bv (N.to_nat (size s)) (N.to_nat (size s))) = false) 
      ->  t = bv_not (zeros (size t)) \/ t = (zeros (size t)))).
Proof. 
  split; intros.
  - destruct H1 as (x, (Hx, A)). split. 
    rewrite <- A. rewrite bv_shl_eq.
    + unfold size. intro HH.
      unfold bv_ashr_a, bv_shl_a. unfold size in *.
      rewrite Hx, H, N.eqb_refl.
      specialize (@length_ashr_aux_a x s (N.to_nat n)); intro Haux.
      rewrite <- Haux, N2Nat.id, N.eqb_refl.
      rewrite length_shl_n_bits_a.
      rewrite <- Haux, N2Nat.id, N.eqb_refl. unfold ashr_aux_a.
      assert (H3: (last 
                    (shl_n_bits_a 
                      (ashr_n_bits_a x (list2nat_be_a s) (last x false)) 
                      (list2nat_be_a s)) 
                    false) =
                  (last x false)).
      { rewrite bv_ult_nat in HH. unfold nat2bv, bv2nat_a, list2nat_be_a in HH.
        rewrite list2N_N2List_s, !Nat2N.id in HH.
        unfold list2nat_be_a, ashr_n_bits_a.
        assert (length s = length x).
        { Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                         (@BV.BVList.RAWBITVECTOR_LIST.bitvector). }
        rewrite <- H1, HH. case_eq ( eqb (last x false) false); intros.
        - rewrite last_skipn_false. easy. rewrite <- H1. easy.
        - rewrite last_skipn_true. easy. rewrite <- H1. easy.
        - Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.size_gt) Reconstr.Empty.
        - rewrite Nat2N.id. unfold nat2bv. rewrite length_N2list.
          Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.eqb_eq) 
                         (@BV.BVList.RAWBITVECTOR_LIST.bitvector). } 
      now rewrite H3, ashr_n_shl_a.
      Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
	    Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
      Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
      Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
   + intro HH. rewrite bv_ult_nat in HH. unfold bv_ashr_a in *.
     rewrite Hx, H, N.eqb_refl in *. unfold ashr_aux_a, ashr_n_bits_a in A.
     unfold bv2nat_a in HH.
     assert ((list2nat_be_a (nat2bv (N.to_nat n) (N.to_nat n)) = length x)%nat).
     { rewrite <- Hx. unfold size. rewrite Nat2N.id. 
       unfold nat2bv, list2nat_be_a. rewrite list2N_N2List_s.
       Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                       @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                      (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                       @BV.BVList.RAWBITVECTOR_LIST.size).
       rewrite Nat.leb_le. specialize (size_gt (length x)); intro HHH.
	     Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_le) 
                (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                 @BV.BVList.RAWBITVECTOR_LIST.size). }
     rewrite H1 in HH. rewrite HH in A.
     case_eq (eqb (last x false) false); intros.
     * rewrite H2 in A. right. 
       Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id)
                      (@BV.BVList.RAWBITVECTOR_LIST.bitvector,
                       @BV.BVList.RAWBITVECTOR_LIST.size, 
                       @BV.BVList.RAWBITVECTOR_LIST.zeros).
     * rewrite H2 in A. left. 
       Reconstr.rcrush (@Coq.NArith.Nnat.Nat2N.id, 
                @BV.BVList.RAWBITVECTOR_LIST.bv_not_false_true) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                @BV.BVList.RAWBITVECTOR_LIST.size, 
                @BV.BVList.RAWBITVECTOR_LIST.zeros).
     * Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.length_nat2bv,
                       @Coq.Arith.PeanoNat.Nat.eqb_eq, @Coq.NArith.Nnat.Nat2N.id) 
                      (@BV.BVList.RAWBITVECTOR_LIST.size, @BV.BVList.RAWBITVECTOR_LIST.bitvector).
  - destruct H1 as (H1, H2).
    case_eq ( bv_ult s (nat2bv (N.to_nat (size s)) (N.to_nat (size s)))); intro HH.
    + exists (bv_shl t s). split.
      * erewrite bv_shl_size with (n := n); easy.
      * now apply H1.
    + specialize (H2 HH). destruct H2 as [H2 | H2].
      * exists (bv_not (zeros (size s))). split.
        { rewrite bv_not_size with (n := n); try easy.
          rewrite zeros_size; easy. }
        { unfold bv_not, bits, zeros. rewrite not_list_false_true.
          unfold bv_ashr_a. unfold size. 
          rewrite length_mk_list_true, N2Nat.id, N.eqb_refl, Nat2N.id.
          unfold ashr_aux_a, ashr_n_bits_a. rewrite bv_ult_nat in HH.
          unfold bv2nat_a, list2nat_be_a, nat2bv in HH.
          rewrite list2N_N2List_s, N2Nat.id in HH. 
          unfold list2nat_be_a. rewrite length_mk_list_true.
          unfold size in HH. rewrite Nat2N.id in HH. rewrite HH.
          case_eq (length s); intros.
          + subst. cbn.
          assert (size t = 0%N).
          { Reconstr.reasy Reconstr.Empty (@Coq.NArith.BinNatDef.N.of_nat, 
                                           @BV.BVList.RAWBITVECTOR_LIST.size). }
          rewrite H in H2. cbn in H2. easy.
          + rewrite last_mk_list_true. cbn.
            unfold bv_not, bits, zeros in H2. rewrite not_list_false_true in H2.
            unfold size in H2. rewrite Nat2N.id in H2.
            assert (length t = length s).
       	   { Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                            (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                             @BV.BVList.RAWBITVECTOR_LIST.size). }
           rewrite H4, H3 in H2. now cbn in H2. easy.
          + unfold size. rewrite !N2Nat.id, !Nat2N.id. apply size_gt.
          + unfold size. rewrite !Nat2N.id. unfold nat2bv.
            rewrite length_N2list. now rewrite Nat.eqb_refl. }
      * exists (zeros (size s)). split.
        { rewrite zeros_size; easy. }
        { unfold zeros. unfold bv_ashr_a. unfold size. 
          rewrite length_mk_list_false, N2Nat.id, N.eqb_refl, Nat2N.id.
          unfold ashr_aux_a, ashr_n_bits_a. rewrite bv_ult_nat in HH.
          unfold bv2nat_a, list2nat_be_a, nat2bv in HH.
          rewrite list2N_N2List_s, N2Nat.id in HH. 
          unfold list2nat_be_a. rewrite length_mk_list_false.
          unfold size in HH. rewrite Nat2N.id in HH. rewrite HH.
          pose proof (@last_mk_list_false (length s)).
          rewrite H3. cbn. unfold bv_not, bits, zeros in H2.
          unfold size in H2. rewrite Nat2N.id in H2.
          assert (length t = length s).
         	{ Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
                           (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                            @BV.BVList.RAWBITVECTOR_LIST.size). }
           now rewrite <- H4. unfold size. rewrite !N2Nat.id, !Nat2N.id. 
           apply size_gt. unfold size. rewrite !Nat2N.id. unfold nat2bv.
           rewrite length_N2list. now rewrite Nat.eqb_refl. }
Qed.

(* (exists x, x >>a s != t) <=> T *)
Theorem bvashr_neq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~(bv_ashr x s = t))
    True.
Proof.
Admitted.

(* (exists x, s >>a x = t) <=> [i=0...size(s)OR(s >>a i = t) *)
Theorem bvashr_eq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ashr s x = t))
    (exists (i : nat), 
(*    (i >= 0) /\ 
      (i <= (N.to_nat (size s))) /\  *)
      ((bv_ashr s (nat2bv i (N.to_nat (size s)))) = t)).
Proof. split; intros.
       - destruct H1 as (x, (H1, H2)).
         exists (bv2nat_a x).
         unfold bv2nat_a. 
         unfold nat2bv, list2nat_be_a.
         rewrite N2Nat.id.
         unfold size in *.
         rewrite H, <- H1, Nat2N.id. now rewrite N2List_list2N.
       - destruct H1 as (i, H1).
         exists (nat2bv i (N.to_nat (size s))). split.
         unfold size. rewrite Nat2N.id.
         now rewrite length_nat2bv.
         easy.
Qed.

(* (exists x, s >>a x != t) 
    <=> 
  (t != 0 or s!= 0) and (t != ~0 or s !- ~0) *)
Theorem bvashr_neq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~(bv_ashr s x = t))
    ((~(t = zeros (size t)) \/ ~(s = zeros (size s)))
      /\
      (~(t = bv_not (zeros (size t))) \/ ~(s = bv_not (zeros (size s))))).
Proof.
Admitted.

(* (exists x, (x >>a s) <u t) <=> (t != 0) *)
Theorem bvashr_ult : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_ashr x s) t))
    (~(t = zeros (size t))).
Proof.
Admitted.

(* (exists x, (s >>a s) <u t) => ((s <u t \/ s >=s 0) /\ t != 0) *)
Theorem bvashr_ult2_rtl : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> 
    (exists (x : bitvector), (size x = n) /\ (bv_ult (bv_ashr_a s x) t = true)) ->
    (((bv_ult s t = true) \/ (bv_slt s (zeros (size s))) = false) /\ 
    (bv_eq t (zeros (size t))) = false).
Proof. 
  intros. split. 
  *** destruct H1 as (x, (H1, H2)).
      rewrite bv_ult_nat in *. unfold bv_ashr_a in *.
      rewrite H, H1, N.eqb_refl in H2.
      unfold ashr_aux_a, list2nat_be_a, ashr_n_bits_a in *.
      case_eq (N.to_nat (list2N x) <? length s); intros. 
      - rewrite H3 in H2.
        case_eq (eqb (last s false) false); intros.
        + rewrite H4 in H2.
          assert ((last s false) = false).
          { destruct ((last s false)); intros; cbn in H4; easy. }
          unfold zeros. 
          specialize (last_mk_list_false (N.to_nat (size s))); intros.
          rewrite bv_slt_ult_last_eq with (d := false); [ | now rewrite H5, H6].
          pose proof (@not_bv_ult_x_zero s). unfold zeros in H7. right. apply H7.
        + rewrite H4 in H2. unfold bv2nat_a, list2nat_be_a, zeros, size in *.
          rewrite Nat2N.id in *. left.
          destruct (n_cases_all (N.to_nat (list2N x))).
          * rewrite H5 in *. rewrite skip0 in H2.
            assert (mk_list_true 0 = nil) by easy.
            now rewrite H6, app_nil_r in H2.
          * destruct (list_cases_all_true s).
            ** rewrite H6 in H2. rewrite skipn_nm in H2; [ | easy].
               now rewrite H6.
            ** specialize (@skipn_gt (N.to_nat (list2N x)) s H5 H3 H6); intros.
               apply Nat.ltb_lt. apply Nat.ltb_lt in H2.
               apply Nat.ltb_lt in H7. lia.
      - rewrite H3 in H2.
        case_eq (eqb (last s false) false); intros.
        + rewrite H4 in H2.
          assert ((last s false) = false).
          { destruct ((last s false)); intros; cbn in H4; easy. }
          unfold zeros.
          specialize (last_mk_list_false (N.to_nat (size s))); intros.
          rewrite bv_slt_ult_last_eq with (d := false); [ | now rewrite H5, H6].
          pose proof (@not_bv_ult_x_zero s). unfold zeros in H7. right. apply H7.
        + rewrite H4 in H2. unfold bv_slt, slt_list.
          unfold bv2nat_a, list2nat_be_a, size in *. left.
          destruct (list_cases_all_true s).
          * now rewrite H5.
          * specialize (@pow_ltb s H5); intros. apply Nat.ltb_lt.
            apply Nat.ltb_lt in H2. apply Nat.ltb_lt in H6. lia.
      - unfold bv_ashr_a. rewrite H, H1, N.eqb_refl.
        specialize (@length_ashr_aux_a s x (N.to_nat n)); intros.
        rewrite <- H3. 
        Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                        @BV.BVList.BITVECTOR_LIST.of_bits_size, 
                        @Coq.Arith.PeanoNat.Nat.eqb_eq) 
                       (@BV.BVList.RAWBITVECTOR_LIST.size,
                        @BV.BVList.RAWBITVECTOR_LIST.bitvector).
        Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                        @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                       (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                        @BV.BVList.RAWBITVECTOR_LIST.size).
        Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                        @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                       (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                        @BV.BVList.RAWBITVECTOR_LIST.size).
      - Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size,
                        @BV.BVList.BITVECTOR_LIST.of_bits_size, 
                        @Coq.Arith.PeanoNat.Nat.eqb_eq) 
                       (@BV.BVList.RAWBITVECTOR_LIST.size, 
                        @BV.BVList.RAWBITVECTOR_LIST.bitvector).
  *** destruct H1 as (x, (H1, H2)). unfold bv_eq. rewrite H0. 
      unfold zeros, size. 
      rewrite length_mk_list_false, N2Nat.id, N.eqb_refl.
      unfold bits. rewrite bv_ult_nat in *. unfold bv_ashr_a in *.
      rewrite H, H1, N.eqb_refl in H2. 
      specialize (@bv2nat_gt0 t (bv2nat_a (ashr_aux_a s x)) H2); intros.
      rewrite <- H0. unfold size. rewrite Nat2N.id.
      now apply List_neq2 in H3. unfold bv_ashr_a.
      rewrite H, H1, N.eqb_refl. 
      specialize (@length_ashr_aux_a s x (N.to_nat n)); intros.
  	  Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.length_ashr_aux_a,
                        @BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                        @BV.BVList.BITVECTOR_LIST.of_bits_size,
                        @Coq.Arith.PeanoNat.Nat.eqb_eq)
                       (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                        @BV.BVList.RAWBITVECTOR_LIST.size).
Qed.

(* (exists x, (s >>a x) <u t) <=> ((s <u t \/ s >=s 0) /\ t != 0) *)
Theorem bvashr_ult2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_ashr s x) t))
    (((bv_ultP s t) \/ ~(bv_sltP s (zeros (size s)))) /\ ~(t = zeros (size t))).
Proof.
Admitted.

(* (exists x, (x >>a s) >u t) <=> (t <u ~0) *)
Theorem bvashr_ugt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_ashr x s) t))
    (bv_ultP t (bv_not (zeros (size t)))).
Proof.
Admitted.

(* (exists x, (s >>a x) >u t) => ((s <s (s >> !t)) \/ (t <u s)) *)
Theorem bvashr_ugt2_rtl: forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> 
    (exists (x : bitvector), (size x = n) /\ (bv_ugt (bv_ashr_a s x) t = true)) ->
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true)).
Proof. 
  intros. destruct H1 as (x, (H1, H2)). apply bv_ugt_bv_ult in H2.
  rewrite bv_ult_nat in *. unfold bv_ashr_a in H2.
  rewrite H, H1, N.eqb_refl in H2.
  unfold ashr_aux_a, list2nat_be_a, ashr_n_bits_a, bv_not in H2.
  case_eq (N.to_nat (list2N x) <? length s); intros.
  - rewrite H3 in H2. case_eq (eqb (last s false) false); intros.
    + rewrite H4 in H2.
      assert ((last s false) = false).
      { destruct ((last s false)); intros; cbn in H4; easy. }
      destruct (n_cases_all (N.to_nat (list2N x))).
      * rewrite H6 in *. rewrite skip0 in H2.
        assert (mk_list_false 0 = nil) by easy.
        rewrite H7, app_nil_r in H2. now right.
        * destruct (list_cases_all_false s).
          ** rewrite H7 in H2.
             rewrite skipn_nm_false in H2; [ | easy].
             rewrite H7. now right.
          ** specialize (@skipn_lt (N.to_nat (list2N x)) s H6 H3 H7); intros.
             right. apply Nat.ltb_lt. apply Nat.ltb_lt in H2.
             apply Nat.ltb_lt in H8. 
             unfold bv2nat_a, list2nat_be_a in *. lia.
    + rewrite H4 in H2. left. unfold bv2nat_a, list2nat_be_a in *.
      rewrite bv_slt_tf. easy. unfold bv_shr_a, size.
      assert ((length s) = (length (bv_not t))).
      { unfold bv_not, bits.
        Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.not_list_length, 
                         @Coq.NArith.Nnat.Nat2N.id) 
                        (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                         @BV.BVList.RAWBITVECTOR_LIST.size). }
      rewrite <- H5, N.eqb_refl.
      Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.length_shr_n_bits_a)
                     (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
      destruct ((last s false)); intros; cbn in H4; easy.
      destruct (list_cases_all_true t).
      * rewrite H5 in H2.
        assert (length (skipn (N.to_nat (list2N x)) s ++ 
                mk_list_true (N.to_nat (list2N x))) = length t). 
        { Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.length_skipn,
                           @Coq.Arith.PeanoNat.Nat.ltb_lt, 
                           @Coq.NArith.Nnat.Nat2N.id, 
                           @Coq.Lists.List.app_length, 
                           @BV.BVList.RAWBITVECTOR_LIST.length_mk_list_true, 
                           @Coq.Arith.PeanoNat.Nat.sub_add, 
                           @Coq.Arith.PeanoNat.Nat.lt_le_incl) 
                          (@BV.BVList.RAWBITVECTOR_LIST.size, 
                           @BV.BVList.RAWBITVECTOR_LIST.bitvector). }
        rewrite <- H6 in H2. now rewrite pow_ltb_false in H2.
      * apply mk_list_false_not_true in H5.
        specialize (@not_mk_list_false (bv_not t)); intros.
        assert ((length (bv_not t)) = length t).
        { Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.not_list_length) 
                         (@BV.BVList.RAWBITVECTOR_LIST.bits,
                          @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                          @BV.BVList.RAWBITVECTOR_LIST.bv_not). }
          rewrite H7 in H6. specialize (H6 H5).
          eapply last_bv_ashr_gt0 with (s:= s) in H6. easy.
          Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.bv_not_size)
          Reconstr.Empty.
  - rewrite H3 in H2.
    case_eq (eqb (last s false) false); intros.
    + rewrite H4 in H2.
      assert ((last s false) = false).
      { destruct ((last s false)); intros; cbn in H4; easy. }
      unfold bv2nat_a, list2nat_be_a in H2.
      rewrite list2N_mk_list_false in H2. easy.
    + rewrite H4 in H2. destruct (list_cases_all_true t).
      * rewrite H5 in H2.
        Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.skipn_same_mktr, 
                        @BV.BVList.RAWBITVECTOR_LIST.skipn_gt_false, 
                        @Coq.NArith.Nnat.Nat2N.id) 
                       (@BV.BVList.RAWBITVECTOR_LIST.list2nat_be_a,
                        @BV.BVList.RAWBITVECTOR_LIST.bv2nat_a, 
                        @BV.BVList.RAWBITVECTOR_LIST.bitvector,
                        @BV.BVList.RAWBITVECTOR_LIST.size).
      * apply mk_list_false_not_true in H5.
        specialize (@not_mk_list_false (bv_not t)); intros.
        assert ((length (bv_not t)) = length t).
        { Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.not_list_length) 
                         (@BV.BVList.RAWBITVECTOR_LIST.bits,
                          @BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                          @BV.BVList.RAWBITVECTOR_LIST.bv_not). }
        rewrite H7 in H6. specialize (H6 H5).
        eapply last_bv_ashr_gt0 with (s:= s) in H6. left.
        rewrite bv_slt_tf. easy. unfold bv_shr_a, size.
        assert ((length s) = (length (bv_not t))).
        { unfold bv_not, bits.
          Reconstr.rcrush (@BV.BVList.RAWBITVECTOR_LIST.not_list_length, 
                           @Coq.NArith.Nnat.Nat2N.id) 
                          (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                           @BV.BVList.RAWBITVECTOR_LIST.size). }
          rewrite <- H8, N.eqb_refl.
          Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.length_shr_n_bits_a)
                         (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
          destruct ((last s false)); intros; cbn in H4; easy. easy.
          Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.bv_not_size) 
          Reconstr.Empty.
  - unfold bv_ashr_a. rewrite H, H1, N.eqb_refl.
    Reconstr.rsimple (@BV.BVList.RAWBITVECTOR_LIST.length_ashr_aux_a,
                      @BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                      @Coq.Arith.PeanoNat.Nat.eqb_eq, 
                      @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                     (@BV.BVList.RAWBITVECTOR_LIST.size,
                      @BV.BVList.RAWBITVECTOR_LIST.bitvector).
  - Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.eqb_eq,
                    @BV.BVList.BITVECTOR_LIST.of_bits_size,
                    @BV.BVList.RAWBITVECTOR_LIST.of_bits_size) 
                   (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
                    @BV.BVList.RAWBITVECTOR_LIST.size).
Qed.

(* (exists x, (s >>a x) >u t) <=> ((s <s (s >> !t)) \/ (t <u s)) *)
Theorem bvashr_ugt2 : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_ashr s x) t))
    ((bv_sltP s (bv_shr s (bv_not t))) \/ (bv_ultP t s)).
Proof.
Admitted.
(*------------------------------------------------------------*)


(*------------------------------Concat------------------------------*)
(* (exists x, x o s = t) <=> s = t[size(s) - 1, 0] *)
(** BE: Please verify this Coq statement with Andy or Cesare *)
Theorem bvconcat_eq : forall (s t : bitvector),
  (size s <= size t)%N ->
  iff
  (exists (x : bitvector), (bv_concat x s) = t)
  (s = bv_extr 0 (size s) (size s) t).
Proof. intros s t Hc.
        split; intro A.
        - destruct A as (x, A).
           rewrite <- A at 1.
           unfold bv_concat, bv_extr.
           case_eq ( (size s <? size s + 0)%N); intros. 
           contradict H. unfold not. rewrite N.add_0_r.
           rewrite N.ltb_irrefl. easy.
           cbn. unfold size.
           assert (N.to_nat (N.of_nat (length s) + 0) = length s).
           lia.
           rewrite H0. now rewrite (extract_app s x).
        - exists (bv_extr (size s) (size t - (size s)) (size t) t). rewrite A at 3.
          unfold bv_concat, bv_extr. unfold size.
          assert ((N.of_nat (length s) <? N.of_nat (length s) + 0)%N = false).
          { rewrite N.add_0_r, N.ltb_irrefl. easy. }
          rewrite H.
          assert ((N.of_nat (length t) <?
          N.of_nat (length t) - N.of_nat (length s) + N.of_nat (length s))%N = false).
          assert ((N.of_nat (length t) - N.of_nat (length s) + N.of_nat (length s))%N = N.of_nat (length t)).
          { rewrite N.sub_add. easy. SearchAbout N.of_nat. easy. }
          rewrite H0, N.ltb_irrefl. easy. 
          assert ((N.to_nat (N.of_nat (length s) + 0)) = length s).
          { rewrite N.add_0_r, Nat2N.id. easy. }
          rewrite H1.
          assert ((N.to_nat (N.of_nat (length s))) = length s).
          { rewrite Nat2N.id. easy. }
          rewrite H2.
          assert ((N.of_nat (length t) - N.of_nat (length s) + N.of_nat (length s))%N = N.of_nat (length t)).
          { rewrite N.sub_add. easy. easy. }
          rewrite H3, N.ltb_irrefl.
          assert ((N.to_nat (N.of_nat (length t))) = length t).
          { rewrite Nat2N.id. easy. }
          rewrite H4. now rewrite extract_app_all.
Qed.

(* (exists x, x o s) != t <=> T *)
Theorem bvconcat_neq : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~((bv_concat x s) = t)) 
    (True).
Proof.
Admitted.

(* (exists x, s o x = t) <=> s = t[size(t) - 1 : size(t) - size(s)] *)
Theorem bvconcat_eq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_concat s x) = t) 
    (s = extract t 
          (N.to_nat(size(t)) - 1) 
          (N.to_nat(size(t)) - N.to_nat(size(s)))).
Proof. 
Admitted.

(* (exists x, s o x != t) <=> T *)
Theorem bvconcat_neq2 : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~((bv_concat s x) = t)) 
    (True).
Proof.
Admitted.

(* (exists x, x o s <u t) <=> 
      ((t[(s(t)-s(x)) : (s(t)-1)] = 0)
        ->
      (s <u t[0 : (s(s)-1)])) *)

(* (exists x, s o x <u t) <=> 
      ((s <=u t[(s(t)-s(s)) : (s(t)-1)]) 
        /\
        ((s = t[(s(t)-s(s)) : (s(t)-1)]
          ->
         t[0 : (s(x)-1)] != 0))) *)

(* (exists x, x o s >u t) <=>
      ((t[s(t)-s(x) : s(t)-1] = !0)
        ->
      (s >u (t[0 : s(s)-1]))) *)

(* (exists x, s o x >u t) <=>
      ((s >=u t[s(t)-s(s) : s(t)-1])
        /\
      ((s = t[s(t)-s(s) : s(t)-1])
        =>
        (t[0 : s(x)-1] != !0))) *)
(*------------------------------------------------------------*)



(* Multiplication, Division, Modulus - Unsolved *)


(*------------------------------Multiplication------------------------------*)
(* (exists x, x.s = t) <=> (-s | s) & t = t *)
Theorem bvmult_eq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_mult x s) = t) 
    ((bv_and (bv_or (bv_not s) s) t) = t).
Proof. intros n s t Hs Hn.
       split; intro A.
       - destruct A as (x, (Hx, A)).
         rewrite <- A.
         unfold bv_or, bv_not, bv_and, bv_mult.
         unfold bits, size in *. rewrite Hx, Hs, N.eqb_refl.
         assert ((N.of_nat (length (map negb s))%N =? n%N)%N = true).
         { unfold negb. rewrite map_length. apply N.eqb_eq.
           easy.
         }
         rewrite H.
         assert (length (mult_list x s) = (length s)).
         { unfold mult_list, bvmult_bool.
           case_eq (length x).
           intros. rewrite and_with_bool_len.
           lia.
           intros n0 Hn0. 
           case n0 in *. rewrite and_with_bool_len.
           lia.
           rewrite prop_mult_bool_step. rewrite and_with_bool_len.
           lia.
         }
         assert ((N.of_nat (length (map2 orb (map negb s) s)) =?
                  N.of_nat (length (mult_list x s)))%N = true).
         { erewrite <- map2_or_length, map_length.
           now rewrite H0, N.eqb_refl.
           now rewrite map_length.
          }
         rewrite H0. rewrite map2_or_neg_true, map2_and_comm.
         rewrite length_mk_list_true, N.eqb_refl.
         now rewrite <- H0, map2_and_1_neutral.
        - admit. (** BE: this case needs unsigned division
                     which is not yet there in the library.
                     The file "th_bv_bitblast.plf" does not
                     contain the signature of bvudiv, please
                     contact Andy asking where to find that
                     signature... *)
Admitted.

(* (exists x, x.s != t) <=> s != 0 or t != 0 *)
Theorem bvmult_neq : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ~((bv_mult x s) = t)) 
    ((~(s = zeros (size s))) \/ (~(t = zeros (size t)))).
Proof.
Admitted.

(* (exists x, x.s <u t) <=> (t != 0) *)
Theorem bvmult_ult : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_mult x s) t))
    (~ t = zeros (size t)).
Proof.
Admitted.

(* (exists x, x.s >u t) <=> (t <u (-s | s)) *)
Theorem bvmult_ugt : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_mult x s) t))
    (bv_ultP t (bv_or (bv_neg s) s)).
Proof.
Admitted.
(*------------------------------------------------------------*)


(*------------------------------Mod------------------------------*)
(* (exists x, x mod s = t) <=> ~(-s) >=u t *)

(* (exists x, x mod s != t) <=> s != 1 or t != 0 *)

(* (exists x, s mod x = t) <=> (t + t - s) & s >=u t *)

(* (exists x, s mod x != t) <=> s != 0 or t != 0 *)

(* (exists x, x mod s <u t) <=> (t != 0) *)

(* (exists x, s mod x <u t) <=> (t != 0) *)

(* (exists x, x mod s >u t) <=> (t <u ~(-s)) *)

(* (exists x, s mod s >u t) <=> (t <u s) *)
(*------------------------------------------------------------*)


(*------------------------------Division------------------------------*)
(* (exists x, x / s = t) <=> (s.t) / s = t *)

(* (exists x, x / s != t) <=>  s != 0 or t!= ~0*)

(* (exists x, s / x = t) <=> s / (s / t) = t *)

(* (exists x, s / x != t  and size(s) = 1) <=> s & t = 0 *)

(* (exists x, s / x != t  and size(s) != 1) <=> T *)

(* (exists x, x / s <u t) <=> ((0 <u s) /\ (0 <u t)) *)

(* (exists x, s / x <u t) <=> ((0 <u ~(-t & s)) /\ (0 <u t)) *)

(* (exists x, x / s >u t) <=> ((~0 / s) >u t) *)

(* (exists x, s / x >u t) <=> (t <u ~0) *)
(*------------------------------------------------------------*)


(*PxTP Goals: *)
(* t != 0 or s <u size(s) => (exists x, x << s != t) *)
Theorem bvshl_neq_ltr : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> 
    (~(t = zeros (size t))
     \/
     ((bv_ult s (nat2bv 
                  (N.to_nat (size s))
                  (N.to_nat (size s)))))
      =
      true)
      ->
    (exists (x : bitvector), (size x = n) /\ ~(bv_shl x s = t)).
Proof.
Admitted.

(* ((s <u t \/ s >=s 0) /\ t != 0) <=> (exists x, (s >>a x) <u t) *)
Theorem bvashr_ult2_ltr : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> 
    (((bv_ultP s t) \/ ~(bv_sltP s (zeros (size s)))) /\ ~(t = zeros (size t)))
          ->
    (exists (x : bitvector), (size x = n) /\ (bv_ultP (bv_ashr s x) t)).
Proof.
Admitted.

(* ((s <s (s >> !t)) \/ (t <u s)) <=> (exists x, (s >>a x) >u t) *)
Theorem bvashr_ugt2_ltr : forall (n : N), forall (s t : bitvector),
  (size s) = n -> (size t) = n -> 
    ((bv_sltP s (bv_shr s (bv_not t))) \/ (bv_ultP t s))
        ->
    (exists (x : bitvector), (size x = n) /\ (bv_ugtP (bv_ashr s x) t)).
Proof.
Admitted.

(* (exists x, (x >> s) >u t) => (t <u (~s >> s)) *)
Theorem bvshr_ugt_rtl : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (exists (x : bitvector), (size x = n) /\ bv_ugtP (bv_shr x s) t)
          ->
    (bv_ultP t (bv_shr (bv_not s) s)).
Proof.
Admitted.