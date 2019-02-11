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
Theorem bvadd : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), ((bv_add x s) = t))
    True.
Proof. 
Admitted.


(*Multiplication*)
(* (exists x, x.s = t) <=> (-s | s) & t = t *)
Theorem bvmult_eq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), (bv_mult x s) = t) 
    ((bv_and (bv_or (bv_not s) s) t) = t).
Proof.
Admitted.

(* (exists x, x.s != t) <=> s != 0 or t != 0 *)
Theorem bvmult_neq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), ~((bv_mult x s) = t)) 
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
Theorem bvand_eq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), (bv_and x s) = t) 
    ((bv_and t s) = t).
Proof.
Admitted.

(* (exists x, x & s != t) <=> s != 0 or t != 0 *)
Theorem bvand_neq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), ~((bv_and x s) = t)) 
    ((bv_and t s) = t).
Proof.
Admitted.

(*Or*)
(* (exists x, x | s = t) <=> t & s = t *)
Theorem bvor_eq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), (bv_or x s) = t) 
    ((bv_and t s) = t).
Proof.
Admitted.

(* (exists x, x | s != t) <=> s != ~0 or t != ~0 *)
Theorem bvor_neq : forall (s t : bitvector), 
   iff 
    (exists (x : bitvector), ~((bv_or x s) = t)) 
    (~(s = (bv_not (zeros (size s)))) 
      \/ 
      (~(t = (bv_not (zeros (size t)))))).
Proof.
Admitted.

(*Logical right shift*)
(* (exists x, x >> s = t) <=> (t << s) >> s = t *)
Theorem bvshr_eq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), bv_shr x s = t) 
    (bv_shr (bv_shl t s) s = t).
Proof.
Admitted.

(* (exists x, x >> s != t) <=> t != 0 or s <u Nat2BV (size(s)) *)
Theorem bvshr_neq : forall (s t : bitvector),
  iff
    (exists (x : bitvector), ~(bv_shr x s = t))
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
(*Theorem bvshr_eq2 : forall (x s t : bitvector),
  iff
    (bv_shr s x = t)
    (Need a way to quantify over integers i...size(s))*)

(* (exists x, s >> x != t) <=> s != 0 or t != 0 *)
Theorem bvshr_neq2 : forall (s t : bitvector),
  iff
    (exists (x : bitvector), ~(bv_shr s x = t))
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
Theorem bvashr_neq : forall (s t : bitvector),
  iff 
    (exists (x : bitvector), ~(bv_ashr x s = t))
    True.
Proof.
Admitted.

(* (exists x, s >>a x = t) <=> [i=0...size(s)OR(s >>a i = t) *)

(* (exists x, s >>a x != t) 
    <=> 
  (t != 0 or s!= 0) and (t != ~0 or s !- ~0) *)
Theorem bvashr_neq2 : forall (s t : bitvector), 
  iff
    (exists (x : bitvector),~(bv_ashr s x = t))
    ((~(t = zeros (size t)) \/ ~(s = zeros (size s)))
      /\
      (~(t = bv_not (zeros (size t))) \/ ~(s = bv_not (zeros (size s))))).
Proof.
Admitted.




(*Logical left shift*)
(* (exists x, x << s = t) <=> (t >> s) << s = t *)
Theorem bvshl_eq : forall (s t : bitvector),
  iff
    (exists (x : bitvector), bv_shl x s = t)
    (bv_shl (bv_shr t s) s = t).
Proof.
Admitted.


(* (exists x, x << s != t) <=> t != 0 or s <u size(s) *)
Theorem bvshl_neq : forall (s t : bitvector),
  iff
    (exists (x : bitvector), ~(bv_shl x s = t))
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
Theorem bvshl_neq2 : forall (s t : bitvector),
  iff
    (exists (x : bitvector), ~(bv_shl s x = t))
    (~(s = zeros (size s)) \/ ~(t = zeros (size t))).
Proof.
Admitted.

(*Concat*)
(* (exists x, x o s = t) <=> s = t[size(s) - 1, 0] *)
Theorem bvconcat_eq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), (bv_concat x s) = t) 
    (s = extract t (N.to_nat(size(s)) - 1) (0)).
Proof.
Admitted.

(* (exists x, x o s) != t <=> T *)
Theorem bvconcat_neq : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), ~((bv_concat x s) = t)) 
    (True).
Proof.
intros s t. (*exists (nil : list bool).
split. 
- intros H. reflexivity.
- intros H. unfold bv_concat.
  induction s as [| hs ts IHs].
  + simpl. *)Admitted.

(* (exists x, s o x = t) <=> s = t[size(t) - 1 : size(t) - size(s)] *)
Theorem bvconcat_eq2 : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), (bv_concat s x) = t) 
    (s = extract t 
          (N.to_nat(size(t)) - 1) 
          (N.to_nat(size(t)) - N.to_nat(size(s)))).
Proof. 
Admitted.

(* (exists x, s o x != t) <=> T *)
Theorem bvconcat_neq2 : forall (s t : bitvector), 
  iff 
    (exists (x : bitvector), ~((bv_concat s x) = t)) 
    (True).
Proof.
intros s t. (*eapply ex_intro.
split.
- intros H. reflexivity.
- intros H.*) Admitted.