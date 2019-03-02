From BV Require Import BVList.

Import RAWBITVECTOR_LIST.

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

From Hammer Require Import Hammer Reconstr.

(* Start Practice:
 forall x : bitvector, size(x) >= 0*)

Theorem length_of_tail : forall (h : bool) (t : list bool), 
 length (h :: t) = S (length t).
Proof. 
  intros h t.
  induction t as [| h' t' IH].
  + reflexivity. 
  + reflexivity. 
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
  (* Lemma non_neg : forall (b : bv), (0 <=u b).
     By @(non_neg (bv_and x s)), 0 <=u (bv_and x s).
     Lemma trans_bv_ult : forall (x, y, z : bv), (x <=u y) -> (y <u z) -> (x <u z).
     By @(trans_bv_ult 0 (x & s) t @(non_neg (x & s)) A), 0 <u t.
     Lemma ult_implies_neq : forall (x, y : bv) x <u y -> x != y.
     By @(ult_implies_neq 0 t), 0 != t. *)
(*+ t != 0 -> exists x, x & s <u t
    exists 0.
    Goal: 0 & s <u t.
    Lemma and_absorb_0 : forall (b : bv), 0 & b = 0.
    By @(and_absorb_0 s), Goal: 0 <u t.
    Lemma nonzero_implies_ltzero forall (b : bv) b != 0 -> 0 <u t.  
    By @(nonzero_implies_ltzero t A), qed. *) 
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
         case_eq (N.to_nat (list2N x 0) =? 0); intros.
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

(* (exists x, (x >> s) >u t) <=> (t <u (~s >> s)) *)
Theorem bvshr_ugt : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n -> iff
    (exists (x : bitvector), (size x = n) /\ bv_ugtP (bv_shr x s) t)
    (bv_ultP t (bv_shr (bv_not s) s)).
Proof.
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
Admitted.

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


(* 
           specialize (@length_ashr_aux_a x s (N.to_nat n)); intro Haux.
           rewrite <- Haux, N2Nat.id, N.eqb_refl.
           rewrite length_shl_n_bits_a.
           rewrite <- Haux, N2Nat.id, N.eqb_refl.
           unfold ashr_aux_a. *)



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
Proof. split; intros.
         - destruct H1 as (x, (Hx, A)).
           split. unfold size. intro HH.
           rewrite <- A. rewrite bv_shl_eq.
           unfold bv_ashr_a, bv_shl_a. unfold size in *.
           rewrite Hx, H, N.eqb_refl.
           specialize (@length_ashr_aux_a x s (N.to_nat n)); intro Haux.
           rewrite <- Haux, N2Nat.id, N.eqb_refl.
           rewrite length_shl_n_bits_a.
           rewrite <- Haux, N2Nat.id, N.eqb_refl.

           unfold ashr_aux_a.
           assert (H3: (last (shl_n_bits_a (ashr_n_bits_a x (list2nat_be_a s) (last x false)) (list2nat_be_a s)) false) =
                    (last x false)) .
           { rewrite bv_ult_nat in HH.
             unfold nat2bv, bv2nat_a, list2nat_be_a in HH.
             rewrite list2N_N2List_s, !Nat2N.id in HH.
             unfold list2nat_be_a, ashr_n_bits_a.
             assert (length s = length x).
             Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
             rewrite <- H1, HH.
             case_eq ( eqb (last x false) false); intros.
             rewrite last_skipn_false. easy.
             rewrite <- H1. easy.
             rewrite last_skipn_true. easy.
             rewrite <- H1. easy.
             Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.size_gt) Reconstr.Empty.
             rewrite Nat2N.id. unfold nat2bv.
             rewrite length_N2list.
             Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.eqb_eq) (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
           } now rewrite H3, ashr_n_shl_a.
           Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
	         Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
        	 Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
           Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.bitvector).
           intro HH. rewrite <- A.
           rewrite bv_ult_nat in HH. unfold bv_ashr_a in *.
           rewrite Hx, H, N.eqb_refl in *.
           unfold ashr_aux_a, ashr_n_bits_a in A.
           unfold bv2nat_a in HH.
           assert ((list2nat_be_a (nat2bv (N.to_nat n) (N.to_nat n)) = length x)%nat).
           { rewrite <- Hx. unfold size.
             rewrite Nat2N.id. unfold nat2bv, list2nat_be_a.
             rewrite list2N_N2List_s.
             Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.of_bits_size, 
                  @BV.BVList.BITVECTOR_LIST.of_bits_size) 
                 (@BV.BVList.RAWBITVECTOR_LIST.bitvector, @BV.BVList.RAWBITVECTOR_LIST.size).
             rewrite Nat.leb_le. specialize (size_gt (length x)); intro HHH.
	           Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_le) 
                (@BV.BVList.RAWBITVECTOR_LIST.bitvector, @BV.BVList.RAWBITVECTOR_LIST.size).
           }
           rewrite H1 in HH. rewrite HH in A.
           case_eq (eqb (last x false) false); intros.
           + rewrite H2 in A.
             right.
             unfold ashr_aux_a, ashr_n_bits_a. rewrite HH, H2.
            Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) 
              (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
               @BV.BVList.RAWBITVECTOR_LIST.size, @BV.BVList.RAWBITVECTOR_LIST.zeros).
           + unfold ashr_aux_a, ashr_n_bits_a. rewrite HH, H2.
             left.
             Reconstr.rcrush (@Coq.NArith.Nnat.Nat2N.id, 
                @BV.BVList.RAWBITVECTOR_LIST.bv_not_false_true) 
               (@BV.BVList.RAWBITVECTOR_LIST.bitvector, @BV.BVList.RAWBITVECTOR_LIST.size, 
                @BV.BVList.RAWBITVECTOR_LIST.zeros).
           + Reconstr.reasy (@BV.BVList.RAWBITVECTOR_LIST.length_nat2bv,
               @Coq.Arith.PeanoNat.Nat.eqb_eq, @Coq.NArith.Nnat.Nat2N.id) 
              (@BV.BVList.RAWBITVECTOR_LIST.size, @BV.BVList.RAWBITVECTOR_LIST.bitvector).
         - destruct H1 as (H1, H2).
           case_eq ( bv_ult s (nat2bv (N.to_nat (size s)) (N.to_nat (size s)))); intro HH.
           exists (bv_shl t s). split.
           erewrite bv_shl_size with (n := n); easy.
           now apply H1.
           specialize (H2 HH). destruct H2 as [H2 | H2].
           exists (bv_not (zeros (size s))). split.
           rewrite bv_not_size with (n := n); try easy.
           rewrite zeros_size; easy.
           unfold bv_not, bits, zeros. rewrite not_list_false_true.
           unfold bv_ashr_a. unfold size. rewrite length_mk_list_true, N2Nat.id, N.eqb_refl, Nat2N.id.
           unfold ashr_aux_a, ashr_n_bits_a.
           rewrite bv_ult_nat in HH.
           unfold bv2nat_a, list2nat_be_a, nat2bv in HH.
           rewrite list2N_N2List_s, N2Nat.id in HH. 
           unfold list2nat_be_a. rewrite length_mk_list_true.
           unfold size in HH. rewrite Nat2N.id in HH.
           rewrite HH.
           
           case_eq (length s); intros.
           subst. cbn.
           assert (size t = 0%N).
           Reconstr.reasy Reconstr.Empty (@Coq.NArith.BinNatDef.N.of_nat, @BV.BVList.RAWBITVECTOR_LIST.size).
           rewrite H in H2. cbn in H2. easy.
           rewrite last_mk_lits_true. cbn.
           unfold bv_not, bits, zeros in H2. rewrite not_list_false_true in H2.
           unfold size in H2. rewrite Nat2N.id in H2.
           assert (length t = length s).
         	 Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
           rewrite H4, H3 in H2. now cbn in H2. easy.
           unfold size. rewrite !N2Nat.id, !Nat2N.id. apply size_gt.
           unfold size. rewrite !Nat2N.id. unfold nat2bv.
           rewrite length_N2list. now rewrite Nat.eqb_refl.
           exists (zeros (size s)). split.
           rewrite zeros_size; easy.
           unfold zeros.
           unfold bv_ashr_a. unfold size. 
           rewrite length_mk_list_false, N2Nat.id, N.eqb_refl, Nat2N.id.
           unfold ashr_aux_a, ashr_n_bits_a.
           rewrite bv_ult_nat in HH.
           unfold bv2nat_a, list2nat_be_a, nat2bv in HH.
           rewrite list2N_N2List_s, N2Nat.id in HH. 
           unfold list2nat_be_a. rewrite length_mk_list_false.
           unfold size in HH. rewrite Nat2N.id in HH.
           rewrite HH.
           assert ( (last (mk_list_false (length s)) false) = false).
           now rewrite last_mk_lits_false.
           rewrite H3. cbn.
           unfold bv_not, bits, zeros in H2.
           unfold size in H2. rewrite Nat2N.id in H2.
           assert (length t = length s).
         	 Reconstr.reasy (@Coq.NArith.Nnat.Nat2N.id) (@BV.BVList.RAWBITVECTOR_LIST.bitvector, 
              @BV.BVList.RAWBITVECTOR_LIST.size).
           now rewrite <- H4.
           unfold size. rewrite !N2Nat.id, !Nat2N.id. apply size_gt.
           unfold size. rewrite !Nat2N.id. unfold nat2bv.
           rewrite length_N2list. now rewrite Nat.eqb_refl.
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

(* (exists x, (s >>a s) <u t) <=> ((s <u t \/ s >=s 0) /\ t != 0) *)
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