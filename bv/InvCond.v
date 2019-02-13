From BV Require Import BVList.

Import RAWBITVECTOR_LIST.

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

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



(*Addition*)
(* (exists x, x + s = t) <=> T *)
Theorem bvadd : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ ((bv_add x s) = t))
    True.
Proof. 
    intros s t n Hs Ht.
    split; intro A.
    - easy.
    - exists (bv_subt' t s).
      split.
      + exact (bv_subt'_size Ht Hs).
      + now rewrite  (bv_add_subst_opp Ht Hs).
Qed.

(** BE: keep this; may be of use *)
Theorem bvadd_U:
  forall (s t x: bitvector) n, (size s) = n /\ (size t) = n /\ (size x) = n ->
  (bv_add x s) = t <-> (x = (bv_subt' t s)).
Proof. intros s t x n (Hs, (Ht, Hx)).
  split; intro A.
  - rewrite <- A. symmetry. exact (@bv_subt'_add n x s Hx Hs).
  - rewrite A. exact (bv_add_subst_opp Ht Hs).
Qed.

(** BE: the same with bvadd *)
Theorem bvadd_e:
  forall (s t : bitvector) n, (size s) = n /\ (size t) = n ->
  exists (x : bitvector), (size x) = n /\ (bv_add x s) = t.
Proof. intros s t n (Hs, Ht).
  exists (bv_subt' t s).
  split; [exact (bv_subt'_size Ht Hs) | exact (bv_add_subst_opp Ht Hs)].
Qed.


(*Multiplication*)
(* (exists x, x.s = t) <=> (-s | s) & t = t *)
Theorem bvmult_eq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> (bv_mult x s) = t) 
    ((bv_and (bv_or (bv_not s) s) t) = t).
Proof.
Admitted.

(* (exists x, x.s != t) <=> s != 0 or t != 0 *)
Theorem bvmult_neq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~((bv_mult x s) = t)) 
    ((~(s = zeros (size s))) \/ (~(t = zeros (size t)))).
Proof.
Admitted.


(*Mod*)
(* (exists x, x mod s = t) <=> ~(-s) >=u t *)

(* (exists x, x mod s != t) <=> s != 1 or t != 0 *)

(* (exists x, s mod x = t) <=> (t + t - s) & s >=u t *)

(* (exists x, s mod x != t) <=> s != 0 or t != 0 *)


(*Division*)
(* (exists x, x / s = t) <=> (s.t) / s = t *)

(* (exists x, x / s != t) <=>  s != 0 or t!= ~0*)

(* (exists x, s / x = t) <=> s / (s / t) = t *)

(* (exists x, s / x != t  and size(s) = 1) <=> s & t = 0 *)

(* (exists x, s / x != t  and size(s) != 1) <=> T *)


(*And*)
(* (exists x, x & s = t) <=> t & s = t*)
(** BE: please verify this statement *)
Theorem bvand_eq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_and x s) = t) 
    ((bv_and t s) = t).
Proof. intros s t n Hs Ht.
       split; intro A.
       - destruct A as (x, (Hx, A)). rewrite <- A.
         now rewrite (@bv_and_comm n x s Hx Hs), (@bv_and_idem1 s x n Hs Hx).
       - exists (bv_and s t). 
         split.
         + rewrite (@bv_and_size n s t); easy.
         + now rewrite (@bv_and_idem1 s t n Hs Ht), (@bv_and_comm n s t Hs Ht).
Qed.

(* (exists x, x & s != t) <=> s != 0 or t != 0 *)
(** BE: statement incorrect? *)
Theorem bvand_neq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_and x s) <> t) 
    (s <> zeros (size s) \/ t <> zeros (size t)).
Proof. intros s t n Hs Ht.
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

(*Or*)
(* (exists x, x | s = t) <=> t & s = t *)
(** BE: please verify this statement *)
Theorem bvor_eq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ (bv_or x s) = t) 
    ((bv_or t s) = t).
Proof. intros s t n Hs Ht.
       split; intro A.
       - destruct A as (x, (Hx, A)). rewrite <- A.
         now rewrite (@bv_or_idem2 x s n Hx Hs).
       - exists t. split; easy.
Qed.

(* (exists x, x | s != t) <=> s != ~0 or t != ~0 *)
Theorem bvor_neq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~((bv_or x s) = t)) 
    (~(s = (bv_not (zeros (size s)))) 
      \/ 
      (~(t = (bv_not (zeros (size t)))))).
Proof.
Admitted.

(*Logical right shift*)
(* (exists x, x >> s = t) <=> (t << s) >> s = t *)
Theorem bvshr_eq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) /\ bv_shr x s = t) 
    (bv_shr (bv_shl t s) s = t).
Proof. intros s t n Hs Ht.
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
Theorem bvshr_neq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~(bv_shr x s = t))
    (~(t = zeros (size t)) 
      \/
      ((bv_ult s (nat2bv 
                  (N.to_nat (size s)) 
                  (N.to_nat (size s))))) 
      = 
      true).
Proof.
Admitted.

(* (exists x, s >> x = t) <=> [i=0...size(s)]OR(s >> i = t) *)
(*Theorem bvshr_eq2 : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> bv_shr s x = t)
    (Need a way to quantify over integers i...size(s))*)

(* (exists x, s >> x != t) <=> s != 0 or t != 0 *)
Theorem bvshr_neq2 : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~(bv_shr s x = t))
    (~(s = zeros (size s))
      \/
     ~(t = zeros (size t))).
Proof.
Admitted.

(*Arithmetic right shift*)
(* (exists x, x >>a s = t) 
      <=> 
  (s <u size(s) => (t << s) >>a s = t) 
    and 
    (s >=u size(s) => (t = ~0 or t = 0)) *)

(* (exists x, x >>a s != t) <=> T *)
Theorem bvashr_neq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~(bv_ashr x s = t))
    True.
Proof.
Admitted.

(* (exists x, s >>a x = t) <=> [i=0...size(s)OR(s >>a i = t) *)

(* (exists x, s >>a x != t) 
    <=> 
  (t != 0 or s!= 0) and (t != ~0 or s !- ~0) *)
Theorem bvashr_neq2 : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~(bv_ashr s x = t))
    ((~(t = zeros (size t)) \/ ~(s = zeros (size s)))
      /\
      (~(t = bv_not (zeros (size t))) \/ ~(s = bv_not (zeros (size s))))).
Proof.
Admitted.


(*Logical left shift*)
(* (exists x, x << s = t) <=> (t >> s) << s = t *)
Theorem bvshl_eq : forall (s t : bitvector) (n : N),
   (size s) = n -> (size t) = n -> iff
     (exists (x : bitvector), (size x = n) /\ bv_shl x s = t)
     (bv_shl (bv_shr t s) s = t).
Proof. intros s t n Hs Ht.
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
Theorem bvshl_neq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~(bv_shl x s = t))
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

(* (exists x, s << x != t) <=> s != 0 or or t != 0 *)
Theorem bvshl_neq2 : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~(bv_shl s x = t))
    (~(s = zeros (size s)) \/ ~(t = zeros (size t))).
Proof.
Admitted.

(*Concat*)
(* (exists x, x o s = t) <=> s = t[size(s) - 1, 0] *)
Theorem bvconcat_eq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> (bv_concat x s) = t) 
    (s = extract t (N.to_nat(size(s)) - 1) (0)).
Proof.
Admitted.

(* (exists x, x o s) != t <=> T *)
Theorem bvconcat_neq : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~((bv_concat x s) = t)) 
    (True).
Proof.
intros s t. (*exists (nil : list bool).
split. 
- intros H. reflexivity.
- intros H. unfold bv_concat.
  induction s as [| hs ts IHs].
  + simpl. *)Admitted.

(* (exists x, s o x = t) <=> s = t[size(t) - 1 : size(t) - size(s)] *)
Theorem bvconcat_eq2 : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> (bv_concat s x) = t) 
    (s = extract t 
          (N.to_nat(size(t)) - 1) 
          (N.to_nat(size(t)) - N.to_nat(size(s)))).
Proof. 
Admitted.

(* (exists x, s o x != t) <=> T *)
Theorem bvconcat_neq2 : forall (s t : bitvector) (n : N), 
  (size s) = n -> (size t) = n -> iff 
    (exists (x : bitvector), (size x = n) -> ~((bv_concat s x) = t)) 
    (True).
Proof.
intros s t. (*eapply ex_intro.
split.
- intros H. reflexivity.
- intros H.*) Admitted.
