(**************************************************************************)
(*                                                                        *)
(*     DTBitVector                                                        *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller  *                                                  *)
(*     Alain   Mebsout ♯                                                  *)
(*     Burak   Ekici   ♯                                                  *)
(*                                                                        *)
(*    * Inria - École Polytechnique - Université Paris-Sud                *)
(*    ♯ The University of Iowa                                            *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.
Require Import Lia.
(*Require Import Misc.*)
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

From Hammer Require Import Hammer Reconstr.

(* We temporarily assume proof irrelevance to handle dependently typed
   bit vectors *)
Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof. intros. lia. Qed.

  Fixpoint leb (n m: nat) : bool :=
    match n with
      | O => 
      match m with
        | O => true
        | S m' => true
      end
      | S n' =>
      match m with
        | O => false
        | S m' => leb n' m'
      end
    end.

Module Type BITVECTOR.

  Parameter bitvector : N -> Type.
  Parameter bits      : forall n, bitvector n -> list bool.
  Parameter of_bits   : forall (l:list bool), bitvector (N.of_nat (List.length l)).
  Parameter bitOf     : forall n, nat -> bitvector n -> bool.

  (* Constants *)
  Parameter zeros     : forall n, bitvector n.
  Parameter one       : forall n, bitvector n.

  (*equality*)
  Parameter bv_eq     : forall n, bitvector n -> bitvector n -> bool.

  (*binary operations*)
  Parameter bv_concat : forall n m, bitvector n -> bitvector m -> bitvector (n + m).
  Parameter bv_and    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_or     : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_xor    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_add    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_subt   : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_mult   : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_ult    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_slt    : forall n, bitvector n -> bitvector n -> bool.

  Parameter bv_ultP   : forall n, bitvector n -> bitvector n -> Prop.
  Parameter bv_sltP   : forall n, bitvector n -> bitvector n -> Prop.

  Parameter bv_shl    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_shr    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_ashr   : forall n, bitvector n -> bitvector n -> bitvector n.

    (*unary operations*)
  Parameter bv_not    : forall n,     bitvector n -> bitvector n.
  Parameter bv_neg    : forall n,     bitvector n -> bitvector n.
  Parameter bv_extr   : forall (i n0 n1 : N), bitvector n1 -> bitvector n0.

 (* Parameter bv_extr   : forall (n i j : N) {H0: n >= j} {H1: j >= i}, bitvector n -> bitvector (j - i). *)

  Parameter bv_zextn  : forall (n i: N), bitvector n -> bitvector (i + n).
  Parameter bv_sextn  : forall (n i: N), bitvector n -> bitvector (i + n).
 (* Parameter bv_extr   : forall n i j : N, bitvector n -> n >= j -> j >= i -> bitvector (j - i). *)

  (* Specification *)
  Axiom bits_size     : forall n (bv:bitvector n), List.length (bits bv) = N.to_nat n.
  Axiom bv_eq_reflect : forall n (a b:bitvector n), bv_eq a b = true <-> a = b.
  Axiom bv_eq_refl    : forall n (a:bitvector n), bv_eq a a = true.

  Axiom bv_ult_B2P    : forall n (a b:bitvector n), bv_ult a b = true <-> bv_ultP a b.
  Axiom bv_slt_B2P    : forall n (a b:bitvector n), bv_slt a b = true <-> bv_sltP a b.
  Axiom bv_ult_not_eq : forall n (a b:bitvector n), bv_ult a b = true -> a <> b.
  Axiom bv_slt_not_eq : forall n (a b:bitvector n), bv_slt a b = true -> a <> b.
  Axiom bv_ult_not_eqP: forall n (a b:bitvector n), bv_ultP a b -> a <> b.
  Axiom bv_slt_not_eqP: forall n (a b:bitvector n), bv_sltP a b -> a <> b.

  Axiom bv_and_comm   : forall n (a b:bitvector n), bv_eq (bv_and a b) (bv_and b a) = true.
  Axiom bv_or_comm    : forall n (a b:bitvector n), bv_eq (bv_or a b) (bv_or b a) = true.
  Axiom bv_add_comm   : forall n (a b:bitvector n), bv_eq (bv_add a b) (bv_add b a) = true. 

  Axiom bv_and_assoc  : forall n (a b c: bitvector n), bv_eq (bv_and a (bv_and b c)) (bv_and (bv_and a b) c) = true.
  Axiom bv_or_assoc   : forall n (a b c: bitvector n), bv_eq (bv_or a (bv_or b c)) (bv_or (bv_or a b) c) = true.
  Axiom bv_xor_assoc  : forall n (a b c: bitvector n), bv_eq (bv_xor a (bv_xor b c)) (bv_xor (bv_xor a b) c) = true.
  Axiom bv_add_assoc  : forall n (a b c: bitvector n), bv_eq (bv_add a (bv_add b c)) (bv_add (bv_add a b) c) = true.
  Axiom bv_not_involutive: forall n (a: bitvector n), bv_eq (bv_not (bv_not a)) a = true.

  Parameter _of_bits  : forall (l: list bool) (s : N), bitvector s.

End BITVECTOR.

Module Type RAWBITVECTOR.

Parameter bitvector  : Type.
Parameter size       : bitvector -> N.
Parameter bits       : bitvector -> list bool.
Parameter of_bits    : list bool -> bitvector.
Parameter _of_bits   : list bool -> N -> bitvector.
Parameter bitOf      : nat -> bitvector -> bool.

(* Constants *)
Parameter zeros      : N -> bitvector.
Parameter one        : N -> bitvector.

(*equality*)
Parameter bv_eq      : bitvector -> bitvector -> bool.

(*binary operations*)
Parameter bv_concat  : bitvector -> bitvector -> bitvector.
Parameter bv_and     : bitvector -> bitvector -> bitvector.
Parameter bv_or      : bitvector -> bitvector -> bitvector.
Parameter bv_xor     : bitvector -> bitvector -> bitvector.
Parameter bv_add     : bitvector -> bitvector -> bitvector.
Parameter bv_mult    : bitvector -> bitvector -> bitvector.
Parameter bv_subt    : bitvector -> bitvector -> bitvector.
Parameter bv_ult     : bitvector -> bitvector -> bool.
Parameter bv_slt     : bitvector -> bitvector -> bool.

Parameter bv_ultP    : bitvector -> bitvector -> Prop.
Parameter bv_sltP    : bitvector -> bitvector -> Prop.

Parameter bv_shl     : bitvector -> bitvector -> bitvector.
Parameter bv_shr     : bitvector -> bitvector -> bitvector.
Parameter bv_ashr    : bitvector -> bitvector -> bitvector.

(*unary operations*)
Parameter bv_not     : bitvector -> bitvector.
Parameter bv_neg     : bitvector -> bitvector.
Parameter bv_extr    : forall (i n0 n1: N), bitvector -> bitvector.

(*Parameter bv_extr    : forall (n i j: N) {H0: n >= j} {H1: j >= i}, bitvector -> bitvector.*)

Parameter bv_zextn   : forall (n i: N), bitvector -> bitvector.
Parameter bv_sextn   : forall (n i: N), bitvector -> bitvector.

(* All the operations are size-preserving *)

Axiom bits_size      : forall bv, List.length (bits bv) = N.to_nat (size bv).
Axiom of_bits_size   : forall l, N.to_nat (size (of_bits l)) = List.length l.
Axiom _of_bits_size  : forall l s,(size (_of_bits l s)) = s.
Axiom zeros_size     : forall n, size (zeros n) = n.
Axiom one_size       : forall n, size (one n) = n.
Axiom bv_concat_size : forall n m a b, size a = n -> size b = m -> size (bv_concat a b) = n + m.
Axiom bv_and_size    : forall n a b, size a = n -> size b = n -> size (bv_and a b) = n.
Axiom bv_or_size     : forall n a b, size a = n -> size b = n -> size (bv_or a b) = n.
Axiom bv_xor_size    : forall n a b, size a = n -> size b = n -> size (bv_xor a b) = n.
Axiom bv_add_size    : forall n a b, size a = n -> size b = n -> size (bv_add a b) = n.
Axiom bv_subt_size   : forall n a b, size a = n -> size b = n -> size (bv_subt a b) = n.
Axiom bv_mult_size   : forall n a b, size a = n -> size b = n -> size (bv_mult a b) = n.
Axiom bv_not_size    : forall n a, size a = n -> size (bv_not a) = n.
Axiom bv_neg_size    : forall n a, size a = n -> size (bv_neg a) = n.
Axiom bv_shl_size    : forall n a b, size a = n -> size b = n -> size (bv_shl a b) = n.
Axiom bv_shr_size    : forall n a b, size a = n -> size b = n -> size (bv_shr a b) = n.
Axiom bv_ashr_size   : forall n a b, size a = n -> size b = n -> size (bv_ashr a b) = n.
Axiom bv_extr_size   : forall i n0 n1 a, size a = n1 -> size (@bv_extr i n0 n1 a) = n0.

(*
Axiom bv_extr_size   : forall n (i j: N) a (H0: n >= j) (H1: j >= i), 
  size a = n -> size (@bv_extr n i j H0 H1 a) = (j - i).
*)

Axiom bv_zextn_size  : forall (n i: N) a, 
  size a = n -> size (@bv_zextn n i a) = (i + n).
Axiom bv_sextn_size  : forall (n i: N) a, 
  size a = n -> size (@bv_sextn n i a) = (i + n).

(* Specification *)
Axiom bv_eq_reflect  : forall a b, bv_eq a b = true <-> a = b.
Axiom bv_eq_refl     : forall a, bv_eq a a = true.


Axiom bv_ult_not_eq  : forall a b, bv_ult a b = true -> a <> b.
Axiom bv_slt_not_eq  : forall a b, bv_slt a b = true -> a <> b.
Axiom bv_ult_not_eqP : forall a b, bv_ultP a b -> a <> b.
Axiom bv_slt_not_eqP : forall a b, bv_sltP a b -> a <> b.
Axiom bv_ult_B2P     : forall a b, bv_ult a b = true <-> bv_ultP a b.
Axiom bv_slt_B2P     : forall a b, bv_slt a b = true <-> bv_sltP a b.


Axiom bv_and_comm    : forall n a b, size a = n -> size b = n -> bv_and a b = bv_and b a.
Axiom bv_or_comm     : forall n a b, size a = n -> size b = n -> bv_or a b = bv_or b a.
Axiom bv_add_comm    : forall n a b, size a = n -> size b = n -> bv_add a b = bv_add b a.

Axiom bv_and_assoc   : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_and a (bv_and b c)) = (bv_and (bv_and a b) c).
Axiom bv_or_assoc    : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_or a (bv_or b c)) = (bv_or (bv_or a b) c).
Axiom bv_xor_assoc   : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_xor a (bv_xor b c)) = (bv_xor (bv_xor a b) c).
Axiom bv_add_assoc   : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                    (bv_add a (bv_add b c)) = (bv_add (bv_add a b) c).
Axiom bv_not_involutive: forall a, bv_not (bv_not a) = a.

End RAWBITVECTOR.

Module RAW2BITVECTOR (M:RAWBITVECTOR) <: BITVECTOR.

  Record bitvector_ (n:N) : Type :=
    MkBitvector
      { bv :> M.bitvector;
        wf : M.size bv = n
      }.
  Definition bitvector := bitvector_.

  Definition bits n (bv:bitvector n) := M.bits bv.

  Lemma of_bits_size l : M.size (M.of_bits l) = N.of_nat (List.length l).
  Proof. now rewrite <- M.of_bits_size, N2Nat.id. Qed.

  Lemma _of_bits_size l s: M.size (M._of_bits l s) = s.
  Proof. apply (M._of_bits_size l s). Qed. 

  Definition of_bits (l:list bool) : bitvector (N.of_nat (List.length l)) :=
    @MkBitvector _ (M.of_bits l) (of_bits_size l).

  Definition _of_bits (l: list bool) (s : N): bitvector s :=
  @MkBitvector _ (M._of_bits l s) (_of_bits_size l s).

  Definition bitOf n p (bv:bitvector n) : bool := M.bitOf p bv.

  Definition zeros (n:N) : bitvector n :=
    @MkBitvector _ (M.zeros n) (M.zeros_size n).

  Definition one (n:N) : bitvector n :=
    @MkBitvector _ (M.one n) (M.one_size n).

  Definition bv_eq n (bv1 bv2:bitvector n) := M.bv_eq bv1 bv2.

  Definition bv_ultP n (bv1 bv2:bitvector n) := M.bv_ultP bv1 bv2.

  Definition bv_sltP n (bv1 bv2:bitvector n) := M.bv_sltP bv1 bv2.

  Definition bv_and n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_and bv1 bv2) (M.bv_and_size (wf bv1) (wf bv2)).

  Definition bv_or n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_or bv1 bv2) (M.bv_or_size (wf bv1) (wf bv2)).

  Definition bv_add n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_add bv1 bv2) (M.bv_add_size (wf bv1) (wf bv2)).

  Definition bv_subt n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_subt bv1 bv2) (M.bv_subt_size (wf bv1) (wf bv2)).

  Definition bv_mult n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_mult bv1 bv2) (M.bv_mult_size (wf bv1) (wf bv2)).

  Definition bv_xor n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_xor bv1 bv2) (M.bv_xor_size (wf bv1) (wf bv2)).

  Definition bv_ult n (bv1 bv2:bitvector n) : bool := M.bv_ult bv1 bv2.

  Definition bv_slt n (bv1 bv2:bitvector n) : bool := M.bv_slt bv1 bv2.

  Definition bv_not n (bv1: bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_not bv1) (M.bv_not_size (wf bv1)).

  Definition bv_neg n (bv1: bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_neg bv1) (M.bv_neg_size (wf bv1)).

  Definition bv_concat n m (bv1:bitvector n) (bv2: bitvector m) : bitvector (n + m) :=
    @MkBitvector (n + m) (M.bv_concat bv1 bv2) (M.bv_concat_size (wf bv1) (wf bv2)).

  Definition bv_extr (i n0 n1: N) (bv1: bitvector n1) : bitvector n0 :=
    @MkBitvector n0 (@M.bv_extr i n0 n1 bv1) (@M.bv_extr_size i n0 n1 bv1 (wf bv1)).

(*
  Definition bv_extr  n (i j: N) (H0: n >= j) (H1: j >= i) (bv1: bitvector n) : bitvector (j - i) :=
    @MkBitvector (j - i) (@M.bv_extr n i j H0 H1 bv1) (@M.bv_extr_size n i j bv1 H0 H1 (wf bv1)).
*)

  Definition bv_zextn n (i: N)  (bv1: bitvector n) : bitvector (i + n) :=
    @MkBitvector (i + n) (@M.bv_zextn n i bv1) (@M.bv_zextn_size n i bv1 (wf bv1)).

  Definition bv_sextn n (i: N)  (bv1: bitvector n) : bitvector (i + n) :=
    @MkBitvector (i + n) (@M.bv_sextn n i bv1) (@M.bv_sextn_size n i bv1 (wf bv1)).

  Definition bv_shl n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_shl bv1 bv2) (M.bv_shl_size (wf bv1) (wf bv2)).

  Definition bv_shr n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_shr bv1 bv2) (M.bv_shr_size (wf bv1) (wf bv2)).

  Definition bv_ashr n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_ashr bv1 bv2) (M.bv_ashr_size (wf bv1) (wf bv2)).

  Lemma bits_size n (bv:bitvector n) : List.length (bits bv) = N.to_nat n.
  Proof. unfold bits. now rewrite M.bits_size, wf. Qed.

  (* The next lemma is provable only if we assume proof irrelevance *)
  Lemma bv_eq_reflect n (a b: bitvector n) : bv_eq a b = true <-> a = b.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. split.
    - revert a b. intros [a Ha] [b Hb]. simpl. intros ->.
      rewrite (proof_irrelevance Ha Hb). reflexivity.
    - intros. case a in *. case b in *. simpl in *.
      now inversion H. (* now intros ->. *)
  Qed.

  Lemma bv_eq_refl n (a : bitvector n) : bv_eq a a = true.
  Proof.
    unfold bv_eq. now rewrite M.bv_eq_reflect.
  Qed.

  Lemma bv_ult_not_eqP: forall n (a b: bitvector n), bv_ultP a b -> a <> b.
  Proof. 
    unfold bv_ultP, bv_ult. intros n a b H.
    apply M.bv_ult_not_eqP in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_slt_not_eqP: forall n (a b: bitvector n), bv_sltP a b -> a <> b.
  Proof. 
    unfold bv_sltP, bv_slt. intros n a b H.
    apply M.bv_slt_not_eqP in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_ult_not_eq: forall n (a b: bitvector n), bv_ult a b = true -> a <> b.
  Proof. 
    unfold bv_ult. intros n a b H.
    apply M.bv_ult_not_eq in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_slt_not_eq: forall n (a b: bitvector n), bv_slt a b = true -> a <> b.
  Proof. 
    unfold bv_slt. intros n a b H.
    apply M.bv_slt_not_eq in H. unfold not in *; intros. apply H.
    apply M.bv_eq_reflect. rewrite H0. apply M.bv_eq_refl.
  Qed.

  Lemma bv_ult_B2P: forall n (a b: bitvector n), bv_ult a b = true <-> bv_ultP a b.
  Proof. 
      unfold bv_ultP, bv_ult; intros; split; intros;
      now apply M.bv_ult_B2P.
  Qed. 

  Lemma bv_slt_B2P: forall n (a b: bitvector n), bv_slt a b = true <-> bv_sltP a b.
  Proof. 
      unfold bv_ultP, bv_slt; intros; split; intros;
      now apply M.bv_slt_B2P.
  Qed.

  Lemma bv_and_comm n (a b:bitvector n) : bv_eq (bv_and a b) (bv_and b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_and_comm n); now rewrite wf.
  Qed.

  Lemma bv_or_comm n (a b:bitvector n) : bv_eq (bv_or a b) (bv_or b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_or_comm n); now rewrite wf.
  Qed.

  Lemma bv_add_comm n (a b:bitvector n) : bv_eq (bv_add a b) (bv_add b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_add_comm n); now rewrite wf.
  Qed.

  Lemma bv_and_assoc : forall n (a b c :bitvector n), bv_eq (bv_and a (bv_and b c)) (bv_and (bv_and a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_and_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_or_assoc : forall n (a b c :bitvector n), bv_eq (bv_or a (bv_or b c)) (bv_or (bv_or a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_or_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_xor_assoc : forall n (a b c :bitvector n), bv_eq (bv_xor a (bv_xor b c)) (bv_xor (bv_xor a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_xor_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_add_assoc : forall n (a b c :bitvector n), bv_eq (bv_add a (bv_add b c)) (bv_add (bv_add a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_add_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_not_involutive: forall n (a: bitvector n), bv_eq (bv_not (bv_not a)) a = true.
  Proof.
       intros n a.
       unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
       apply (@M.bv_not_involutive a); now rewrite wf.
  Qed.


End RAW2BITVECTOR.

Module RAWBITVECTOR_LIST <: RAWBITVECTOR.

Definition bitvector := list bool.
Definition bits (a:bitvector) : list bool := a.
Definition size (a:bitvector) := N.of_nat (List.length a).
Definition of_bits (a:list bool) : bitvector := a.

Lemma bits_size bv : List.length (bits bv) = N.to_nat (size bv).
Proof. unfold bits, size. now rewrite Nat2N.id. Qed.

Lemma of_bits_size l : N.to_nat (size (of_bits l)) = List.length l.
Proof. unfold of_bits, size. now rewrite Nat2N.id. Qed.

Fixpoint beq_list (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => true
    | x :: l', y :: m' => (Bool.eqb x y) && (beq_list l' m')
    | _, _ => false
  end.

Definition bv_eq (a b: bitvector): bool:=
  if ((size a) =? (size b)) then beq_list (bits a) (bits b) else false.

Fixpoint beq_listP (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => True
    | x :: l', y :: m' => (x = y) /\ (beq_listP l' m')
    | _, _ => False
  end.


Lemma bv_mk_eq l1 l2 : bv_eq l1 l2 = beq_list l1 l2.
Proof.
  unfold bv_eq, size, bits.
  case_eq (Nat.eqb (length l1) (length l2)); intro Heq.
  - now rewrite (EqNat.beq_nat_true _ _ Heq), N.eqb_refl.
  - replace (N.of_nat (length l1) =? N.of_nat (length l2)) with false.
    * revert l2 Heq. induction l1 as [ |b1 l1 IHl1]; intros [ |b2 l2]; simpl in *; auto.
      intro Heq. now rewrite <- (IHl1 _ Heq), andb_false_r.
    * symmetry. rewrite N.eqb_neq. intro H. apply Nat2N.inj in H. rewrite H in Heq.
      rewrite <- EqNat.beq_nat_refl in Heq. discriminate.
Qed.
Definition bv_concat (a b: bitvector) : bitvector := b ++ a.

Section Map2.

  Variables A B C: Type.
  Variable f : A -> B -> C.

  Fixpoint map2 (l1 : list A) (l2 : list B) {struct l1} : list C :=
    match l1, l2 with
      | b1::tl1, b2::tl2 => (f b1 b2)::(map2 tl1 tl2)
      | _, _ => nil
    end.

End Map2.

Section Fold_left2.

  Variables A B: Type.
  Variable f : A -> B -> B -> A.

  Fixpoint fold_left2 (xs ys: list B) (acc:A) {struct xs} : A :=
    match xs, ys with
    | nil, _ | _, nil => acc
    | x::xs, y::ys    => fold_left2 xs ys (f acc x y)
    end.

  Lemma foo : forall (I: A -> Prop) acc, I acc -> 
              (forall a b1 b2, I a -> I (f a b1 b2)) -> 
              forall xs ys, I (fold_left2 xs ys acc).
  Proof. intros I acc H0 H1 xs. revert acc H0.
         induction xs as [ | a xs IHxs]; intros acc H.
         simpl. auto.
         intros [ | b ys].
            + simpl. exact H.
            + simpl. apply IHxs, H1. exact H.
  Qed.

Fixpoint mk_list_true_acc (t: nat) (acc: list bool) : list bool :=
  match t with
    | O    => acc
    | S t' => mk_list_true_acc t' (true::acc)
  end.

Fixpoint mk_list_true (t: nat) : list bool :=
  match t with
    | O    => []
    | S t' => true::(mk_list_true t')
  end.

Fixpoint mk_list_false_acc (t: nat) (acc: list bool) : list bool :=
  match t with
    | O    => acc
    | S t' => mk_list_false_acc t' (false::acc)
  end.

Fixpoint mk_list_false (t: nat) : list bool :=
  match t with
    | O    => []
    | S t' => false::(mk_list_false t')
  end.

Definition zeros (n : N) : bitvector := mk_list_false (N.to_nat n).

End Fold_left2.

Fixpoint mk_list_one (t: nat) : list bool := 
  match t with
    | O => []
    | S O => [true]
    | S t' => false :: (mk_list_one t')
  end.

Definition one (n : N) : bitvector := rev (mk_list_one (N.to_nat n)).

Definition bitOf (n: nat) (a: bitvector): bool := nth n a false.

Definition bv_and (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 andb (@bits a) (@bits b)
    | _    => nil
  end.

Definition bv_or (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 orb (@bits a) (@bits b)
    | _    => nil
  end.

Definition bv_xor (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 xorb (@bits a) (@bits b)
    | _    => nil
  end.

Definition bv_not (a: bitvector) : bitvector := map negb (@bits a).


(*arithmetic operations*)

 (*addition*)

Definition add_carry b1 b2 c :=
  match b1, b2, c with
    | true,  true,  true  => (true, true)
    | true,  true,  false
    | true,  false, true
    | false, true,  true  => (false, true)
    | false, false, true
    | false, true,  false
    | true,  false, false => (true, false)
    | false, false, false => (false, false)
  end.

(* Truncating addition in little-endian, direct style *)

Fixpoint add_list_ingr bs1 bs2 c {struct bs1} :=
  match bs1, bs2 with
    | nil, _               => nil
    | _ , nil              => nil
    | b1 :: bs1, b2 :: bs2 =>
      let (r, c) := add_carry b1 b2 c in r :: (add_list_ingr bs1 bs2 c)
  end.

Definition add_list (a b: list bool) := add_list_ingr a b false.

Definition bv_add (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => add_list a b
    | _    => nil
  end.

  (*substraction*)

Definition twos_complement b :=
  add_list_ingr (map negb b) (mk_list_false (length b)) true.
  
Definition bv_neg (a: bitvector) : bitvector := (twos_complement a).

Definition subst_list' a b := add_list a (twos_complement b).

Definition bv_subt' (a b : bitvector) : bitvector :=
   match (@size a) =? (@size b) with
     | true => (subst_list' (@bits a) (@bits b))
     | _    => nil
   end.

Definition subst_borrow b1 b2 b :=
  match b1, b2, b with
    | true,  true,  true  => (true, true)
    | true,  true,  false => (false, false)
    | true,  false, true  => (false, false)
    | false, true,  true  => (false, true)
    | false, false, true  => (true, true)
    | false, true,  false => (true, true)
    | true,  false, false => (true, false)
    | false, false, false => (false, false)
  end.

Fixpoint subst_list_borrow bs1 bs2 b {struct bs1} :=
  match bs1, bs2 with
    | nil, _               => nil
    | _ , nil              => nil
    | b1 :: bs1, b2 :: bs2 =>
      let (r, b) := subst_borrow b1 b2 b in r :: (subst_list_borrow bs1 bs2 b)
  end.

Definition subst_list (a b: list bool) := subst_list_borrow a b false.

Definition bv_subt (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with 
    | true => subst_list (@bits a) (@bits b)
    | _    => nil 
  end.
  
(*less than*)

Fixpoint ult_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: nil, yi :: nil => andb (negb xi) yi
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (ult_list_big_endian x' y'))
          (andb (negb xi) yi)
  end.

Definition ult_list (x y: list bool) :=
  (ult_list_big_endian (List.rev x) (List.rev y)).


Fixpoint slt_list_big_endian (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: nil, yi :: nil => andb xi (negb yi)
    | xi :: x', yi :: y' =>
      orb (andb (Bool.eqb xi yi) (ult_list_big_endian x' y'))
          (andb xi (negb yi))
  end.

Definition slt_list (x y: list bool) :=
  slt_list_big_endian (List.rev x) (List.rev y).


Definition bv_ult (a b : bitvector) : bool :=
  if @size a =? @size b then ult_list a b else false.


Definition bv_slt (a b : bitvector) : bool :=
  if @size a =? @size b then slt_list a b else false.

Definition ult_listP (x y: list bool) :=
  if ult_list x y then True else False.

Definition slt_listP (x y: list bool) :=
  if slt_list x y then True else False.

Definition bv_ultP (a b : bitvector) : Prop :=
  if @size a =? @size b then ult_listP a b else False.

Definition bv_sltP (a b : bitvector) : Prop :=
  if @size a =? @size b then slt_listP a b else False.

  (*multiplication*)

Fixpoint mult_list_carry (a b :list bool) n {struct a}: list bool :=
  match a with
    | nil      => mk_list_false n
    | a' :: xs =>
      if a' then
        add_list b (mult_list_carry xs (false :: b) n)
      else
        mult_list_carry xs (false :: b) n
  end.

Fixpoint mult_list_carry2 (a b :list bool) n {struct a}: list bool :=
  match a with
    | nil      => mk_list_false n
    | a' :: xs =>
      if a' then
        add_list b (mult_list_carry2 xs (false :: (removelast b)) n)
      else
        mult_list_carry2 xs (false :: (removelast b)) n
  end.
  
Fixpoint and_with_bool (a: list bool) (bt: bool) : list bool :=
  match a with
    | nil => nil
    | ai :: a' => (bt && ai) :: and_with_bool a' bt 
  end.

Fixpoint mult_bool_step_k_h (a b: list bool) (c: bool) (k: Z) : list bool :=
  match a, b with
    | nil , _ => nil
    | ai :: a', bi :: b' =>
      if ((k - 1)%Z <? 0)%Z then
        let carry_out := (ai && bi) || ((xorb ai bi) && c) in
        let curr := xorb (xorb ai bi) c in
        curr :: mult_bool_step_k_h a' b' carry_out (k - 1)
      else
        ai :: mult_bool_step_k_h a' b c (k - 1)
    | ai :: a' , nil => ai :: mult_bool_step_k_h a' b c k
  end.

Fixpoint top_k_bools (a: list bool) (k: Z) : list bool :=
  if (Z.eqb k 0) then nil
  else match a with
         | nil => nil
         | ai :: a' => ai :: top_k_bools a' (k - 1)
       end.

Fixpoint mult_bool_step (a b: list bool) (res: list bool) (k k': nat) : list bool :=
  let ak := List.firstn (S k') a in
  let b' := and_with_bool ak (nth k b false) in
  let res' := mult_bool_step_k_h res b' false (Z.of_nat k) in
  match k' with
    | O => res'
    (* | S O => res' *)
    | S pk' => mult_bool_step a b res' (S k) pk'
  end.

Definition bvmult_bool (a b: list bool) (n: nat) : list bool :=
  let res := and_with_bool a (nth 0 b false) in
  match n with
    | O => res
    | S O => res
    | S (S k) => mult_bool_step a b res 1 k
  end.

Definition mult_list a b := bvmult_bool a b (length a).

Definition bv_mult (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then mult_list a b
  else nil.

(* Theorems *)

Lemma length_mk_list_false: forall n, length (mk_list_false n) = n.
Proof. intro n.
       induction n as [ | n' IHn].
       - simpl. auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma length_mk_list_one: forall n, length (rev (mk_list_one n)) = n.
Proof. intro n.
  induction n as [| n' IHn].
  - reflexivity.
  - assert (H: forall n, length (rev (mk_list_one (S n))) = S (length (rev(mk_list_one n)))).
    { intros n. rewrite -> rev_length. rewrite -> rev_length. induction n as [ | n'' IHn'].
      + reflexivity.
      + reflexivity. }
    rewrite -> H. rewrite -> IHn. reflexivity.
Qed.

Definition _of_bits (a:list bool) (s: N) := 
if (N.of_nat (length a) =? s) then a else zeros s.

Lemma _of_bits_size l s: (size (_of_bits l s)) = s.
Proof. unfold of_bits, size. unfold _of_bits.
       case_eq ( N.of_nat (length l) =? s).
       intros. now rewrite N.eqb_eq in H.
       intros. unfold zeros. rewrite length_mk_list_false.
       now rewrite N2Nat.id.
Qed.

Lemma length_mk_list_true: forall n, length (mk_list_true n) = n.
Proof. intro n.
       induction n as [ | n' IHn].
       - simpl. auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma zeros_size (n : N) : size (zeros n) = n.
Proof. unfold size, zeros. now rewrite length_mk_list_false, N2Nat.id. Qed. 

Lemma one_size (n : N) : size (one n) = n.
Proof. unfold size. unfold one. rewrite length_mk_list_one.
  rewrite N2Nat.id. reflexivity. Qed.

Lemma List_eq : forall (l m: list bool), beq_list l m = true <-> l = m.
Proof.
    induction l; destruct m; simpl; split; intro; try (reflexivity || discriminate).
    - rewrite andb_true_iff in H. destruct H. rewrite eqb_true_iff in H. rewrite H.
    apply f_equal. apply IHl. exact H0.
    - inversion H. subst b. subst m. rewrite andb_true_iff. split.
      + apply eqb_reflx.
      + apply IHl; reflexivity.
Qed.

Lemma List_eqP : forall (l m: list bool), beq_listP l m  <-> l = m.
Proof.
    induction l; destruct m; simpl; split; intro; try (reflexivity || discriminate); try now contradict H.
    - destruct H. rewrite H.
      apply f_equal. apply IHl. exact H0.
    - inversion H. subst b. subst m. split.
      + reflexivity.
      + apply IHl; reflexivity.
Qed.

Lemma List_eq_refl : forall (l: list bool), beq_list l l = true.
Proof.
    induction l; simpl; try (reflexivity || discriminate).
    - rewrite andb_true_iff. split. apply eqb_reflx. apply IHl.
Qed.

Lemma List_eqP_refl : forall (l: list bool), beq_listP l l  <-> l = l.
Proof. intro l.
       induction l as [ | xl xsl IHl ]; intros.
       - easy.
       - simpl. repeat split. now apply IHl.
Qed.

Lemma List_neq : forall (l m: list bool), beq_list l m = false -> l <> m.
Proof. 
       intro l.
       induction l.
       - intros. case m in *; simpl. now contradict H. easy.
       - intros. simpl in H.
         case_eq m; intros; rewrite H0 in H. 
           easy. simpl.
           case_eq (Bool.eqb a b); intros.
           rewrite H1 in H. rewrite andb_true_l in H.
           apply Bool.eqb_prop in H1.
           specialize (IHl l0 H).
           rewrite H1. 
           unfold not in *.
           intros. apply IHl.
           now inversion H2.
           apply Bool.eqb_false_iff in H1.
           unfold not in *.
           intros. apply H1.
           now inversion H2.
Qed.

Lemma List_neqP : forall (l m: list bool), ~beq_listP l m -> l <> m.
Proof. 
       intro l.
       induction l.
       - intros. case m in *; simpl. now contradict H. easy.
       - intros. unfold not in H. simpl in H.
         case_eq m; intros. easy.
         rewrite H0 in H.
         unfold not. intros. apply H. inversion H1.
         split; try easy.
         now apply List_eqP_refl.
Qed.

Lemma bv_eq_reflect a b : bv_eq a b = true <-> a = b.
Proof.
  unfold bv_eq. case_eq (size a =? size b); intro Heq; simpl.
  - apply List_eq.
  - split; try discriminate.
    intro H. rewrite H, N.eqb_refl in Heq. discriminate.
Qed.

Lemma bv_eq_refl a: bv_eq a a = true.
Proof.
  unfold bv_eq. rewrite N.eqb_refl. now apply List_eq. 
Qed.

Lemma bv_concat_size n m a b : size a = n -> size b = m -> size (bv_concat a b) = (n + m)%N.
Proof.
  unfold bv_concat, size. intros H0 H1.
  rewrite app_length, Nat2N.inj_add, H0, H1; now rewrite N.add_comm.
Qed.

(*list bitwise AND properties*)

Lemma map2_and_comm: forall (a b: list bool), (map2 andb a b) = (map2 andb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' = b' && a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply andb_comm.
Qed.

Lemma map2_and_assoc: forall (a b c: list bool), (map2 andb a (map2 andb b c)) = (map2 andb (map2 andb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (a' && (b' && c') = a' && b' && c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply andb_assoc.
Qed.

Lemma map2_and_idem1:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && a' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite andb_comm, andb_assoc, andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem_comm:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem1. Qed.

Lemma map2_and_idem2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && b' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite <- andb_assoc. rewrite andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem_comm2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem2. Qed.

Lemma map2_and_empty_empty1:  forall (a: list bool), (map2 andb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_and_empty_empty2:  forall (a: list bool), (map2 andb [] a) = [].
Proof. intros a. rewrite map2_and_comm. apply map2_and_empty_empty1. Qed.

Lemma map2_nth_empty_false:  forall (i: nat), nth i [] false = false.
Proof. intros i. induction i as [ | IHi]; simpl; reflexivity. Qed.

Lemma mk_list_true_equiv: forall t acc, mk_list_true_acc t acc = (List.rev (mk_list_true t)) ++ acc.
Proof. induction t as [ |t IHt]; auto; intro acc; simpl; rewrite IHt.
       rewrite app_assoc_reverse.
       apply f_equal. simpl. reflexivity.
Qed.

Lemma mk_list_false_equiv: forall t acc, mk_list_false_acc t acc = (List.rev (mk_list_false t)) ++ acc.
Proof. induction t as [ |t IHt]; auto; intro acc; simpl; rewrite IHt. 
       rewrite app_assoc_reverse.
       apply f_equal. simpl. reflexivity.
Qed.

Lemma len_mk_list_true_empty: length (mk_list_true_acc 0 []) = 0%nat.
Proof. simpl. reflexivity. Qed.

Lemma add_mk_list_true: forall n acc, length (mk_list_true_acc n acc) = (n + length acc)%nat.
Proof. intros n.
       induction n as [ | n' IHn].
         + auto.
         + intro acc. simpl. rewrite IHn. simpl. lia.
Qed.

Lemma map2_and_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 andb a b) false = (nth i a false) && (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_and_empty_empty2.
             rewrite map2_nth_empty_false. reflexivity.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_and_empty_empty1.
             rewrite map2_nth_empty_false. rewrite andb_false_r. reflexivity.
           + intros i H0 H1. simpl.
             revert i H1. induction i as [ | i IHi].
             * simpl. auto.
             * intros. apply IHxs.
                 inversion H0; reflexivity.
                 inversion H1; lia.
Qed.

Lemma length_mk_list_true_full: forall n, length (mk_list_true_acc n []) = n.
Proof. intro n. rewrite (@add_mk_list_true n []). auto. Qed.

Lemma mk_list_app: forall n acc, mk_list_true_acc n acc = mk_list_true_acc n [] ++ acc.
Proof. intro n.
       induction n as [ | n IHn].
         + auto.
         + intro acc. simpl in *. rewrite IHn. 
           cut (mk_list_true_acc n [] ++ [true] = mk_list_true_acc n [true]). intro H.
           rewrite <- H. rewrite <- app_assoc. unfold app. reflexivity.
           rewrite <- IHn. reflexivity.
Qed.

Lemma mk_list_ltrue: forall n, mk_list_true_acc n [true] = mk_list_true_acc (S n) [].
Proof. intro n. induction n as [ | n IHn]; auto. Qed.

Lemma map2_and_1_neutral: forall (a: list bool), (map2 andb a (mk_list_true (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite andb_true_r. reflexivity.
Qed.

Lemma map2_and_0_absorb: forall (a: list bool), (map2 andb a (mk_list_false (length a))) = (mk_list_false (length a)).
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite andb_false_r; reflexivity.
Qed.

Lemma map2_and_length: forall (a b: list bool), length a = length b -> length a = length (map2 andb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

(*bitvector AND properties*)

Lemma bv_and_size n a b : size a = n -> size b = n -> size (bv_and a b) = n.
Proof.
  unfold bv_and. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_and_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_and_comm n a b : size a = n -> size b = n -> bv_and a b = bv_and b a.
Proof.
  intros H1 H2. unfold bv_and. rewrite H1, H2.
  rewrite N.eqb_compare, N.compare_refl.
  rewrite map2_and_comm. reflexivity.
Qed.

Lemma bv_and_assoc: forall n a b c, size a = n -> size b = n -> size c = n -> 
                                  (bv_and a (bv_and b c)) = (bv_and (bv_and a b) c).
Proof. intros n a b c H0 H1 H2.
       unfold bv_and, size, bits in *. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite H0. rewrite N.compare_refl.
       rewrite <- (@map2_and_length a b). rewrite <- map2_and_length. rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite map2_and_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_and_idem1:  forall a b n, size a = n -> size b = n -> (bv_and (bv_and a b) a) = (bv_and a b).
Proof. intros a b n H0 H1.
        unfold bv_and. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_and_length. rewrite N.compare_refl. 
       rewrite map2_and_idem1; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_and_idem2: forall a b n, size a = n ->  size b = n -> (bv_and (bv_and a b) b) = (bv_and a b).
Proof. intros a b n H0 H1.
       unfold bv_and. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_and_length. rewrite N.compare_refl. 
       rewrite map2_and_idem2; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Definition bv_empty: bitvector := nil.

Lemma bv_and_empty_empty1: forall a, (bv_and a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty, bv_and, size, bits. simpl.
       rewrite map2_and_empty_empty1.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a))) in H.
           rewrite H. simpl. reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_and_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_and a b)) false = (nth i (bits a) false) && (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_and. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_and_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_and_empty_empty2: forall a, (bv_and bv_empty a) = bv_empty.
Proof. intro a. unfold bv_and, bv_empty, size.
       case (length a); simpl; auto.
Qed.

Lemma bv_and_1_neutral: forall a, (bv_and a (mk_list_true (length (bits a)))) = a.
Proof. intro a. unfold bv_and.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_true.
       rewrite N.compare_refl.
       rewrite map2_and_1_neutral. reflexivity.
Qed.

Lemma bv_and_0_absorb: forall a, (bv_and a (mk_list_false (length (bits a)))) = (mk_list_false (length (bits a))).
Proof. intro a. unfold bv_and.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_false. 
       rewrite N.compare_refl.
       rewrite map2_and_0_absorb. reflexivity.
Qed.

(* lists bitwise OR properties *)

Lemma map2_or_comm: forall (a b: list bool), (map2 orb a b) = (map2 orb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' = b' || a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply orb_comm.
Qed.

Lemma map2_or_assoc: forall (a b c: list bool), (map2 orb a (map2 orb b c)) = (map2 orb (map2 orb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (a' || (b' || c') = a' || b' || c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply orb_assoc.
Qed.

Lemma map2_or_length: forall (a b: list bool), length a = length b -> length a = length (map2 orb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_or_empty_empty1:  forall (a: list bool), (map2 orb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_or_empty_empty2:  forall (a: list bool), (map2 orb [] a) = [].
Proof. intros a. rewrite map2_or_comm. apply map2_or_empty_empty1. Qed.

Lemma map2_or_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 orb a b) false = (nth i a false) || (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_or_empty_empty2.
             rewrite map2_nth_empty_false. contradict H1. simpl. unfold not. intros. easy.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_or_empty_empty1.
             rewrite map2_nth_empty_false. rewrite orb_false_r. rewrite H0 in H1.
             contradict H1. simpl. unfold not. intros. easy.
           + intros i H0 H1. simpl.
             revert i H1. induction i as [ | i IHi].
             * simpl. auto.
             * intros. apply IHxs.
                 inversion H0; reflexivity.
                 inversion H1; lia.
Qed.

Lemma map2_or_0_neutral: forall (a: list bool), (map2 orb a (mk_list_false (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite orb_false_r. reflexivity.
Qed.

Lemma map2_or_1_true: forall (a: list bool), (map2 orb a (mk_list_true (length a))) = (mk_list_true (length a)).
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite orb_true_r; reflexivity.
Qed.

Lemma map2_or_idem1:  forall (a b: list bool), (map2 orb (map2 orb a b) a) = (map2 orb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' || a' = a' || b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite orb_comm, orb_assoc, orb_diag. reflexivity. 
Qed.

Lemma map2_or_idem2:  forall (a b: list bool), (map2 orb (map2 orb a b) b) = (map2 orb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' || b' = a' || b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite <- orb_assoc. rewrite orb_diag. reflexivity. 
Qed.

Lemma map2_or_neg_true:  forall (a: list bool), (map2 orb (map negb a) a) = mk_list_true (length a).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn.
         assert (negb a || a = true).
         case a; easy.
         now rewrite H, IHa.
Qed.

(*bitvector OR properties*)

Lemma bv_or_size n a b : size a = n -> size b = n -> size (bv_or a b) = n.
Proof.
  unfold bv_or. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_or_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_comm: forall n a b, (size a) = n -> (size b) = n -> bv_or a b = bv_or b a.
Proof. intros a b n H0 H1. unfold bv_or.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_or_comm. reflexivity.
Qed.

Lemma bv_or_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_or a (bv_or b c)) = (bv_or (bv_or a b) c).
Proof. intros n a b c H0 H1 H2. 
       unfold bv_or. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@map2_or_length b c).
       rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- (@map2_or_length a b).
       rewrite H0. rewrite N.compare_refl.
       rewrite map2_or_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_empty_empty1: forall a, (bv_or a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty. 
       unfold bv_or, bits, size. simpl.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a)) 0) in H.
           rewrite H. simpl. rewrite map2_or_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_or_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_or a b)) false = (nth i (bits a) false) || (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_or. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_or_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_or_0_neutral: forall a, (bv_or a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_or.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite map2_or_0_neutral. reflexivity.
Qed.

Lemma bv_or_1_true: forall a, (bv_or a (mk_list_true (length (bits a)))) = (mk_list_true (length (bits a))).
Proof. intro a. unfold bv_or.
       rewrite N.eqb_compare.  unfold size, bits. rewrite length_mk_list_true.
       rewrite N.compare_refl.
       rewrite map2_or_1_true. reflexivity.
Qed.


Lemma bv_or_idem1:  forall a b n, size a = n -> size b = n -> (bv_or (bv_or a b) a) = (bv_or a b).
Proof. intros a b n H0 H1.
       unfold bv_or. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_or_length. rewrite N.compare_refl. 
       rewrite map2_or_idem1; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_idem2: forall a b n, size a = n ->  size b = n -> (bv_or (bv_or a b) b) = (bv_or a b).
Proof. intros a b n H0 H1.
       unfold bv_or. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_or_length. rewrite N.compare_refl. 
       rewrite map2_or_idem2; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.


(* lists bitwise XOR properties *)

Lemma map2_xor_comm: forall (a b: list bool), (map2 xorb a b) = (map2 xorb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (xorb a' b' = xorb b' a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply xorb_comm.
Qed.

Lemma map2_xor_assoc: forall (a b c: list bool), (map2 xorb a (map2 xorb b c)) = (map2 xorb (map2 xorb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (xorb a' (xorb b' c') = (xorb (xorb a'  b')  c')). intro H. rewrite <- H. apply f_equal.
            apply IHxs. rewrite xorb_assoc_reverse. reflexivity.
Qed.

Lemma map2_xor_length: forall (a b: list bool), length a = length b -> length a = length (map2 xorb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_xor_empty_empty1:  forall (a: list bool), (map2 xorb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_xor_empty_empty2:  forall (a: list bool), (map2 xorb [] a) = [].
Proof. intros a. rewrite map2_xor_comm. apply map2_xor_empty_empty1. Qed.

Lemma map2_xor_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 xorb a b) false = xorb (nth i a false) (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_xor_empty_empty2.
             rewrite map2_nth_empty_false. contradict H1. simpl. unfold not. intros. easy.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_xor_empty_empty1.
             rewrite map2_nth_empty_false. rewrite xorb_false_r. rewrite H0 in H1.
             contradict H1. simpl. unfold not. intros. easy.
           + intros i H0 H1. simpl.
             revert i H1. induction i as [ | i IHi].
             * simpl. auto.
             * intros. apply IHxs.
                 inversion H0; reflexivity.
                 inversion H1; lia.
Qed.

Lemma map2_xor_0_neutral: forall (a: list bool), (map2 xorb a (mk_list_false (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite xorb_false_r. reflexivity.
Qed.

Lemma map2_xor_1_true: forall (a: list bool), (map2 xorb a (mk_list_true (length a))) = map negb a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs. rewrite <- IHxs.
         rewrite xorb_true_r; reflexivity.
Qed.

(*bitvector OR properties*)

Lemma bv_xor_size n a b : size a = n -> size b = n -> size (bv_xor a b) = n.
Proof.
  unfold bv_xor. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_xor_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_xor_comm: forall n a b, (size a) = n -> (size b) = n -> bv_xor a b = bv_xor b a.
Proof. intros n a b H0 H1. unfold bv_xor.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_xor_comm. reflexivity.
Qed.

Lemma bv_xor_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_xor a (bv_xor b c)) = (bv_xor (bv_xor a b) c).
Proof. intros n a b c H0 H1 H2. 
       unfold bv_xor. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@map2_xor_length b c).
       rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- (@map2_xor_length a b).
       rewrite H0. rewrite N.compare_refl.
       rewrite map2_xor_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_xor_empty_empty1: forall a, (bv_xor a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty. 
       unfold bv_xor, bits, size. simpl.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a)) 0) in H.
           rewrite H. simpl. rewrite map2_xor_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_xor_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_xor a b)) false = xorb (nth i (bits a) false) (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_xor. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_xor_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_xor_0_neutral: forall a, (bv_xor a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_xor.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite map2_xor_0_neutral. reflexivity.
Qed.

Lemma bv_xor_1_true: forall a, (bv_xor a (mk_list_true (length (bits a)))) = map negb a.
Proof. intro a. unfold bv_xor.
       rewrite N.eqb_compare.  unfold size, bits. rewrite length_mk_list_true.
       rewrite N.compare_refl.
       rewrite map2_xor_1_true. reflexivity.
Qed.

(*bitwise NOT properties*)

Lemma not_list_length: forall a, length a = length (map negb a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto. 
       - simpl. apply f_equal. exact IHxs.
Qed.

Lemma not_list_involutative: forall a, map negb (map negb a) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]; auto.
       simpl. rewrite negb_involutive. apply f_equal. exact IHxs.
Qed.

Lemma not_list_false_true: forall n, map negb (mk_list_false n) = mk_list_true n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_true_false: forall n, map negb (mk_list_true n) = mk_list_false n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_and_or: forall a b, map negb (map2 andb a b) = map2 orb (map negb a) (map negb b).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - intros [ | b ys].
         + auto.
         + simpl. rewrite negb_andb. apply f_equal. apply IHxs.
Qed.

Lemma not_list_or_and: forall a b, map negb (map2 orb a b) = map2 andb (map negb a) (map negb b).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - intros [ | b ys].
         + auto.
         + simpl. rewrite negb_orb. apply f_equal. apply IHxs.
Qed.

(*bitvector NOT properties*)

Lemma bv_not_size: forall n a, (size a) = n -> size (bv_not a) = n.
Proof. intros n a H. unfold bv_not.
       unfold size, bits in *. rewrite <- not_list_length. exact H.
Qed.

Lemma bv_not_involutive: forall a, bv_not (bv_not a) = a.
Proof. intro a. unfold bv_not.
       unfold size, bits. rewrite not_list_involutative. reflexivity.
Qed.

Lemma bv_not_false_true: forall n, bv_not (mk_list_false n) = (mk_list_true n).
Proof. intros n. unfold bv_not.
       unfold size, bits. rewrite not_list_false_true. reflexivity.
Qed.

Lemma bv_not_true_false: forall n, bv_not (mk_list_true n) = (mk_list_false n).
Proof. intros n. unfold bv_not.
       unfold size, bits. rewrite not_list_true_false. reflexivity.
Qed.

Lemma bv_not_and_or: forall n a b, (size a) = n -> (size b) = n -> bv_not (bv_and a b) = bv_or (bv_not a) (bv_not b).
Proof. intros n a b H0 H1. unfold bv_and in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or, size, bits in *.
       do 2 rewrite <- not_list_length. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not, size, bits in *. 
       rewrite not_list_and_or. reflexivity.
Qed.

Lemma bv_not_or_and: forall n a b, (size a) = n -> (size b) = n -> bv_not (bv_or a b) = bv_and (bv_not a) (bv_not b).
Proof. intros n a b H0 H1. unfold bv_and, size, bits in *. 
       do 2 rewrite <- not_list_length.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or, size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not, size, bits in *.
       rewrite not_list_or_and. reflexivity.
Qed.

(* list bitwise ADD properties*)

Lemma add_carry_ff: forall a, add_carry a false false = (a, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_f: forall a, add_carry a (negb a) false = (true, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_f_r: forall a, add_carry (negb a) a false = (true, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_t: forall a, add_carry a (negb a) true = (false, true).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_tt: forall a, add_carry a true true = (a, true).
Proof. intro a. case a; auto. Qed.

Lemma add_list_empty_l: forall (a: list bool), (add_list [] a) = [].
Proof. intro a. induction a as [ | a xs IHxs].
         - unfold add_list. simpl. reflexivity.
         - apply IHxs.
Qed.

Lemma add_list_empty_r: forall (a: list bool), (add_list a []) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_ingr_l: forall (a: list bool) (c: bool), (add_list_ingr [] a c) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_ingr_r: forall (a: list bool) (c: bool), (add_list_ingr a [] c) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_carry_comm: forall (a b:  list bool) (c: bool), add_list_ingr a b c = add_list_ingr b a c.
Proof. intros a. induction a as [ | a' xs IHxs]; intros b c.
       - simpl. rewrite add_list_ingr_r. reflexivity.
       - case b as [ | b' ys].
         + simpl. auto.
         + simpl in *. cut (add_carry a' b' c = add_carry b' a' c).
           * intro H. rewrite H. destruct (add_carry b' a' c) as (r, c0).
             rewrite IHxs. reflexivity.
           * case a', b', c;  auto.
Qed.

Lemma add_list_comm: forall (a b: list bool), (add_list a b) = (add_list b a).
Proof. intros a b. unfold add_list. apply (add_list_carry_comm a b false). Qed.

Lemma add_list_carry_assoc: forall (a b c:  list bool) (d1 d2 d3 d4: bool),
                            add_carry d1 d2 false = add_carry d3 d4 false ->
                            (add_list_ingr (add_list_ingr a b d1) c d2) = (add_list_ingr a (add_list_ingr b c d3) d4).
Proof. intros a. induction a as [ | a' xs IHxs]; intros b c d1 d2 d3 d4.
       - simpl. reflexivity.
       - case b as [ | b' ys].
         + simpl. auto.
         + case c as [ | c' zs].
           * simpl. rewrite add_list_ingr_r. auto.
           * simpl.
             case_eq (add_carry a' b' d1); intros r0 c0 Heq0. simpl.
             case_eq (add_carry r0 c' d2); intros r1 c1 Heq1.
             case_eq (add_carry b' c' d3); intros r3 c3 Heq3.
             case_eq (add_carry a' r3 d4); intros r2 c2 Heq2.
             intro H. rewrite (IHxs _ _ c0 c1 c3 c2);
               revert Heq0 Heq1 Heq3 Heq2;
               case a', b', c', d1, d2, d3, d4; simpl; do 4 (intros H'; inversion_clear H'); 
                 try reflexivity; simpl in H; discriminate.
Qed.

Lemma add_list_carry_length_eq: forall (a b: list bool) c, length a = length b -> length a = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. inversion H; reflexivity.
Qed.

Lemma add_list_carry_length_ge: forall (a b: list bool) c, (length a >= length b)%nat -> length b = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. intros b H0 H1. lia.
       intros [ | b ys].
       - simpl. intros. auto.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. lia.
Qed.

Lemma add_list_carry_length_le: forall (a b: list bool) c, (length b >= length a)%nat -> length a = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. intros b H0 H1. reflexivity.
       intros [ | b ys].
       - simpl. intros. contradict H. lia.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. lia.
Qed.

Lemma bv_neg_size: forall n a, (size a) = n -> size (bv_neg a) = n.
Proof. intros n a H. unfold bv_neg.
       unfold size, bits in *. unfold twos_complement.
       specialize (@add_list_carry_length_eq  (map negb a) (mk_list_false (length a)) true).
       intros. rewrite <- H0. now rewrite map_length.
       rewrite map_length.
       now rewrite length_mk_list_false.
Qed.

Lemma length_add_list_eq: forall (a b: list bool), length a = length b -> length a = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_eq a b false). exact H. Qed.

Lemma length_add_list_ge: forall (a b: list bool), (length a >= length b)%nat -> length b = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_ge a b false). exact H. Qed.

Lemma length_add_list_le: forall (a b: list bool), (length b >= length a)%nat -> length a = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_le a b false). exact H. Qed.

Lemma add_list_assoc: forall (a b c: list bool), (add_list (add_list a b) c) = (add_list a (add_list b c)).
Proof. intros a b c. unfold add_list.
       apply (@add_list_carry_assoc a b c false false false false).
       simpl; reflexivity.
Qed.

Lemma add_list_carry_empty_neutral_n_l: forall (a: list bool) n, (n >= (length a))%nat -> (add_list_ingr (mk_list_false n) a false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - intro n. rewrite add_list_ingr_r. reflexivity.
       - intros [ | n]. 
         + simpl. intro H. contradict H. easy.
         + simpl. intro H.
           case a'; apply f_equal; apply IHxs; lia.
Qed.

Lemma add_list_carry_empty_neutral_n_r: forall (a: list bool) n, (n >= (length a))%nat -> (add_list_ingr a (mk_list_false n) false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - intro n. rewrite add_list_ingr_l. reflexivity.
       - intros [ | n]. 
         + simpl. intro H. contradict H. easy.
         + simpl. intro H.
           case a'; apply f_equal; apply IHxs; lia.
Qed.

Lemma add_list_carry_empty_neutral_l: forall (a: list bool), (add_list_ingr (mk_list_false (length a)) a false) = a.
Proof. intro a.
       rewrite add_list_carry_empty_neutral_n_l; auto.
Qed.

Lemma add_list_carry_empty_neutral_r: forall (a: list bool), (add_list_ingr a (mk_list_false (length a)) false) = a.
Proof. intro a.
       rewrite add_list_carry_empty_neutral_n_r; auto.
Qed.

Lemma add_list_empty_neutral_n_l: forall (a: list bool) n, (n >= (length a))%nat -> (add_list (mk_list_false n) a) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_n_l a).
Qed.

Lemma add_list_empty_neutral_n_r: forall (a: list bool) n, (n >= (length a))%nat -> (add_list a (mk_list_false n)) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_n_r a).
Qed.

Lemma add_list_empty_neutral_r: forall (a: list bool), (add_list a (mk_list_false (length a))) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_r a).
Qed.

Lemma add_list_empty_neutral_l: forall (a: list bool), (add_list (mk_list_false (length a)) a) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_l a).
Qed.

Lemma add_list_carry_unit_t : forall a, add_list_ingr a (mk_list_true (length a)) true = a.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. case_eq (add_carry a true true). intros r0 c0 Heq0.
         rewrite add_carry_tt in Heq0. inversion Heq0.
         apply f_equal. exact IHxs.
Qed.

Lemma add_list_carry_twice: forall a c, add_list_ingr a a c = removelast (c :: a).
Proof. intro a. 
       induction a as [ | a xs IHxs].
       - intros c. simpl. reflexivity.
       - intros [ | ].
         + simpl. case a.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
         + simpl. case a.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
Qed.

Lemma add_list_twice: forall a, add_list a a = removelast (false :: a).
Proof. intro a. 
       unfold add_list. rewrite add_list_carry_twice. reflexivity.
Qed.

(*bitvector ADD properties*)

Lemma bv_add_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_add a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_add. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@length_add_list_eq a b). auto.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_add_comm: forall n a b, (size a) = n -> (size b) = n -> bv_add a b = bv_add b a.
Proof. intros n a b H0 H1.
       unfold bv_add, size, bits in *. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_comm. reflexivity.
Qed.

Lemma bv_add_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_add a (bv_add b c)) = (bv_add (bv_add a b) c).
Proof. intros n a b c H0 H1 H2.
       unfold bv_add, size, bits in *. rewrite H1, H2.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@length_add_list_eq b c). rewrite H0, H1.
       rewrite N.compare_refl. rewrite N.eqb_compare.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@length_add_list_eq a b). rewrite H0.
       rewrite N.compare_refl.
       rewrite add_list_assoc. reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_add_empty_neutral_l: forall a, (bv_add (mk_list_false (length (bits a))) a) = a.
Proof. intro a. unfold bv_add, size, bits. 
       rewrite N.eqb_compare. rewrite length_mk_list_false. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_l. reflexivity.
Qed.

Lemma bv_add_empty_neutral_r: forall a, (bv_add a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_add, size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_r. reflexivity.
Qed.

Lemma bv_add_twice: forall a, bv_add a a = removelast (false :: a).
Proof. intro a. unfold bv_add, size, bits.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_twice. reflexivity.
Qed.

(* bitwise SUBST properties *)

Lemma subst_list_empty_empty_l: forall a, (subst_list [] a) = [].
Proof. intro a. unfold subst_list; auto. Qed.

Lemma subst_list_empty_empty_r: forall a, (subst_list a []) = [].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - unfold subst_list; auto. 
Qed.

Lemma subst_list'_empty_empty_r: forall a, (subst_list' a []) = [].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - unfold subst_list' in *. unfold twos_complement. simpl. reflexivity.
Qed.

Lemma subst_list_borrow_length: forall (a b: list bool) c, length a = length b -> length a = length (subst_list_borrow a b c). 
Proof. induction a as [ | a' xs IHxs]. 
       simpl. auto. 
       intros [ | b ys].
       - simpl. intros. exact H. 
       - intros. simpl in *. 
         case_eq (subst_borrow a' b c); intros r c0 Heq. simpl. apply f_equal. 
         specialize (@IHxs ys). apply IHxs. inversion H; reflexivity. 
Qed.

Lemma length_twos_complement: forall (a: list bool), length a = length (twos_complement a).
Proof. intro a.
      induction a as [ | a' xs IHxs].
      - auto.
      - unfold twos_complement. specialize (@add_list_carry_length_eq (map negb (a' :: xs)) (mk_list_false (length (a' :: xs))) true).        
        intro H. rewrite <- H. simpl. apply f_equal. rewrite <- not_list_length. reflexivity.
        rewrite length_mk_list_false. rewrite <- not_list_length. reflexivity.
Qed.

Lemma subst_list_length: forall (a b: list bool), length a = length b -> length a = length (subst_list a b). 
Proof. intros a b H. unfold subst_list. apply (@subst_list_borrow_length a b false). exact H. Qed.

Lemma subst_list'_length: forall (a b: list bool), length a = length b -> length a = length (subst_list' a b).
Proof. intros a b H. unfold subst_list'.
       rewrite <- (@length_add_list_eq a (twos_complement b)).
       - reflexivity.
       - rewrite <- (@length_twos_complement b). exact H.
Qed.

Lemma subst_list_borrow_empty_neutral: forall (a: list bool), (subst_list_borrow a (mk_list_false (length a)) false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl.
         cut(subst_borrow a' false false = (a', false)).
         + intro H. rewrite H. rewrite IHxs. reflexivity.
         + unfold subst_borrow. case a'; auto.
Qed.

Lemma subst_list_empty_neutral: forall (a: list bool), (subst_list a (mk_list_false (length a))) = a.
Proof. intros a. unfold subst_list.
       apply (@subst_list_borrow_empty_neutral a).
Qed.

Lemma twos_complement_cons_false: forall a, false :: twos_complement a = twos_complement (false :: a).
Proof. intro a.
       induction a as [ | a xs IHxs]; unfold twos_complement; simpl; reflexivity.
Qed.

Lemma twos_complement_false_false: forall n, twos_complement (mk_list_false n) = mk_list_false n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. rewrite <- twos_complement_cons_false.
         apply f_equal. exact IHn.
Qed.

Lemma subst_list'_empty_neutral: forall (a: list bool), (subst_list' a (mk_list_false (length a))) = a.
Proof. intros a. unfold subst_list'.
       rewrite (@twos_complement_false_false (length a)).
       rewrite add_list_empty_neutral_r. reflexivity.
Qed.

(* some list ult and slt properties *)

Lemma ult_list_big_endian_trans : forall x y z,
    ult_list_big_endian x y = true ->
    ult_list_big_endian y z = true ->
    ult_list_big_endian x z = true.
Proof.
  intros x. induction x.
  simpl. easy.
  intros y z.
  case y.
  simpl. case x; easy.
  intros b l.
  intros.
  simpl in *. case x in *.
  case z in *. simpl in H0. case l in *; easy.
  case l in *.
  rewrite andb_true_iff in H.
  destruct H.
  apply negb_true_iff in H. subst.
  simpl. case z in *. easy.
  rewrite !orb_true_iff, !andb_true_iff in H0.
  destruct H0.
  destruct H.
  apply Bool.eqb_prop in H.
  subst.
  rewrite orb_true_iff. now right.
  destruct H. easy.
  rewrite !orb_true_iff, !andb_true_iff in H, H0.
  destruct H.
  simpl in H. easy.
  destruct H.
  apply negb_true_iff in H. subst.
  simpl.
  destruct H0.
  destruct H.
  apply Bool.eqb_prop in H.
  subst.
  case z; easy.
  destruct H. easy.
  case l in *.
  rewrite !orb_true_iff, !andb_true_iff in H.
  simpl in H. destruct H. destruct H. case x in H1; easy.
  destruct H.
  apply negb_true_iff in H. subst.
  simpl in H0.
  case z in *; try easy.
  case z in *; simpl in H0; try easy.
  case b in H0; simpl in H0; try easy.
  case z in *; try easy.
  rewrite !orb_true_iff, !andb_true_iff in *.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  apply Bool.eqb_prop in H.
  apply Bool.eqb_prop in H0.
  subst.
  left.
  split.
  apply Bool.eqb_reflx.
  now apply (IHx (b1 :: l) z H1 H2).
  right. apply Bool.eqb_prop in H. now subst.
  right. destruct H0, H0.
  apply Bool.eqb_prop in H0. now subst.
  split; easy.
Qed.  
  

Lemma ult_list_trans : forall x y z,
    ult_list x y = true -> ult_list y z = true -> ult_list x z = true.
Proof. unfold ult_list. intros x y z. apply ult_list_big_endian_trans.
Qed.

Lemma ult_list_big_endian_not_eq : forall x y,
    ult_list_big_endian x y = true -> x <> y.
Proof.
  intros x. induction x.
  simpl. easy.
  intros y.
  case y.
  simpl. case x; easy.
  intros b l.
  simpl.
  specialize (IHx l).
  case x in *.
  simpl.
  case l in *. case a; case b; simpl; easy.
  easy.
  rewrite !orb_true_iff, !andb_true_iff.
  intro.
  destruct H.
  destruct H.
  apply IHx in H0.
  apply Bool.eqb_prop in H.
  rewrite H in *.
  unfold not in *; intro.
  inversion H1; subst. now apply H0.
  destruct H.
  apply negb_true_iff in H. subst. easy.
Qed.  

Lemma ult_list_not_eq : forall x y, ult_list x y = true -> x <> y.
Proof. unfold ult_list.
  unfold not. intros.
  apply ult_list_big_endian_not_eq in H.
  subst. auto.
Qed.

Lemma slt_list_big_endian_not_eq : forall x y,
    slt_list_big_endian x y = true -> x <> y.
Proof.
  intros x. induction x.
  simpl. easy.
  intros y.
  case y.
  simpl. case x; easy.
  intros b l.
  simpl.
  specialize (IHx l).
  case x in *.
  simpl.
  case l in *. case a; case b; simpl; easy.
  easy.
  rewrite !orb_true_iff, !andb_true_iff.
  intro.
  destruct H.
  destruct H.
  apply ult_list_big_endian_not_eq in H0.
  apply Bool.eqb_prop in H. rewrite H in *.
  unfold not in *. intros. apply H0. now inversion H1.
  destruct H.
  apply negb_true_iff in H0. subst. easy.
Qed.  

Lemma slt_list_not_eq : forall x y, slt_list x y = true -> x <> y.
Proof. unfold slt_list.
  unfold not. intros.
  apply slt_list_big_endian_not_eq in H.
  subst. auto.
Qed.


Lemma ult_list_not_eqP : forall x y, ult_listP x y -> x <> y.
Proof. unfold ult_listP.
  unfold not. intros. unfold ult_list in H.
  case_eq (ult_list_big_endian (List.rev x) (List.rev y)); intros.
  apply ult_list_big_endian_not_eq in H1. subst. now contradict H1.
  now rewrite H1 in H.
Qed.

Lemma slt_list_not_eqP : forall x y, slt_listP x y -> x <> y.
Proof. unfold slt_listP.
  unfold not. intros. unfold slt_list in H.
  case_eq (slt_list_big_endian (List.rev x) (List.rev y)); intros.
  apply slt_list_big_endian_not_eq in H1. subst. now contradict H1.
  now rewrite H1 in H.
Qed.

Lemma bv_ult_B2P: forall x y, bv_ult x y = true <-> bv_ultP x y.
Proof. intros. split; intros; unfold bv_ult, bv_ultP in *.
       case_eq (size x =? size y); intros;
       rewrite H0 in H; unfold ult_listP. now rewrite H.
       now contradict H.
       unfold ult_listP in *.
       case_eq (size x =? size y); intros.
       rewrite H0 in H.
       case_eq (ult_list x y); intros. easy.
       rewrite H1 in H. now contradict H.
       rewrite H0 in H. now contradict H.
Qed.

Lemma bv_slt_B2P: forall x y, bv_slt x y = true <-> bv_sltP x y.
Proof. intros. split; intros; unfold bv_slt, bv_sltP in *.
       case_eq (size x =? size y); intros;
       rewrite H0 in H; unfold slt_listP. now rewrite H.
       now contradict H.
       unfold slt_listP in *.
       case_eq (size x =? size y); intros.
       rewrite H0 in H.
       case_eq (slt_list x y); intros. easy.
       rewrite H1 in H. now contradict H.
       rewrite H0 in H. now contradict H.
Qed.

Lemma nlt_be_neq_gt: forall x y,
    length x = length y -> ult_list_big_endian x y = false ->
    beq_list x y = false -> ult_list_big_endian y x = true.
Proof. intro x.
       induction x as [ | x xs IHxs ].
       - intros. simpl in *. case y in *; now contradict H. 
       - intros.
         simpl in H1.

         case_eq y; intros.
         rewrite H2 in H. now contradict H.
         simpl.
         case_eq l. intros. case_eq xs. intros.
         rewrite H2 in H1.
         rewrite H4 in H0, H. simpl in H0, H.
         rewrite H2, H3 in H0, H.
         rewrite H4, H3 in H1. simpl in H1. rewrite andb_true_r in H1.
         case b in *; case x in *; easy.
         intros.
         rewrite H4, H2, H3 in H. now contradict H.
         intros.
         rewrite H2, H3 in H0, H1.

         simpl in H0.
         case_eq xs. intros. rewrite H4, H2, H3 in H. now contradict H.
         intros. rewrite H4 in H0.
         rewrite <- H3, <- H4.
         rewrite <- H3, <- H4 in H0.
         rewrite <- H3 in H1.
         rewrite orb_false_iff in H0.
         destruct H0.

         case_eq (Bool.eqb x b); intros.
         rewrite H6 in H0, H1.
         rewrite andb_true_l in H0, H1.
         assert (Bool.eqb b x = true).
          { case b in *; case x in *; easy. }
         rewrite H7. rewrite andb_true_l.
         rewrite orb_true_iff.
         left.
         apply IHxs. rewrite H2 in H.
         now inversion H.
         easy. easy.
         assert (Bool.eqb b x = false). 
           { case b in *; case x in *; easy. }
         rewrite H7. rewrite orb_false_l.
         case x in *. case b in *.
         now contradict H6.
         now easy.
         case b in *.
         now contradict H5.
         now contradict H6.
Qed.


(** bitvector ult/slt *)

Lemma bv_ult_not_eqP : forall x y, bv_ultP x y -> x <> y.
Proof. intros x y. unfold bv_ultP.
       case_eq (size x =? size y); intros.
       - now apply ult_list_not_eqP in H0.
       - now contradict H0.
Qed.

Lemma bv_slt_not_eqP : forall x y, bv_sltP x y -> x <> y.
Proof. intros x y. unfold bv_sltP.
       case_eq (size x =? size y); intros.
       - now apply slt_list_not_eqP in H0.
       - now contradict H0.
Qed.

Lemma bv_ult_not_eq : forall x y, bv_ult x y = true -> x <> y.
Proof. intros x y. unfold bv_ult.
       case_eq (size x =? size y); intros.
       - now apply ult_list_not_eq in H0.
       - now contradict H0.
Qed.

Lemma bv_slt_not_eq : forall x y, bv_slt x y = true -> x <> y.
Proof. intros x y. unfold bv_slt.
       case_eq (size x =? size y); intros.
       - now apply slt_list_not_eq in H0.
       - now contradict H0.
Qed.

Lemma rev_eq: forall x y, beq_list x y = true ->
                     beq_list (List.rev x) (List.rev y)  = true.
Proof. intros.
       apply List_eq in H.
       rewrite H.
       now apply List_eq_refl.
Qed.

Lemma rev_neq: forall x y, beq_list x y = false ->
                      beq_list (List.rev x) (List.rev y) = false.
Proof. intros.
       specialize (@List_neq x y H).
       intros.
       apply not_true_is_false.
       unfold not in *.
       intros. apply H0.
       apply List_eq in H1.

       specialize (f_equal (@List.rev bool) H1 ).
       intros.
       now rewrite !rev_involutive in H2.
Qed.

Lemma nlt_neq_gt: forall x y,
    length x = length y -> ult_list x y = false -> 
    beq_list x y = false -> ult_list y x = true.
Proof. intros.
  unfold ult_list in *.
  apply nlt_be_neq_gt.
  now rewrite !rev_length.
  easy. 
  now apply rev_neq in H1.
Qed.


(* bitvector SUBT properties *)

Lemma bv_subt_size: forall n a b, size a = n -> size b = n -> size (bv_subt a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_subt, size, bits in *. rewrite H0, H1. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- subst_list_length. exact H0.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_subt_empty_neutral_r: forall a, (bv_subt a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_subt, size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite subst_list_empty_neutral. reflexivity.
Qed.

Lemma bv_subt'_size: forall n a b, (size a) = n -> (size b) = n -> size (bv_subt' a b) = n.
Proof. intros n a b H0 H1. unfold bv_subt', size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- subst_list'_length. exact H0.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_subt'_empty_neutral_r: forall a, (bv_subt' a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_subt', size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite subst_list'_empty_neutral. reflexivity.
Qed.

(* bitwise ADD-NEG properties *)

Lemma add_neg_list_carry_false: forall a b c, add_list_ingr a (add_list_ingr b c true) false = add_list_ingr a (add_list_ingr b c false) true.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. auto.
       - case b as [ | b ys].
         + simpl. auto.
         + case c as [ | c zs].
           * simpl. auto.
           * simpl.
             case_eq (add_carry b c false); intros r0 c0 Heq0.
             case_eq (add_carry b c true); intros r1 c1 Heq1.
             case_eq (add_carry a r1 false); intros r2 c2 Heq2.
             case_eq (add_carry a r0 true); intros r3 c3 Heq3.
             case a, b, c; inversion Heq0; inversion Heq1; 
             inversion Heq2; inversion Heq3; rewrite <- H2 in H4; 
             rewrite <- H0 in H5; inversion H4; inversion H5; apply f_equal;
             try reflexivity; rewrite IHxs; reflexivity.
Qed.


Lemma add_neg_list_carry_neg_f: forall a, (add_list_ingr a (map negb a) false) = mk_list_true (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry a (negb a) false); intros r0 c0 Heq0.
         rewrite add_carry_neg_f in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry_neg_f_r: forall a, (add_list_ingr (map negb a) a false) = mk_list_true (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry (negb a) a false); intros r0 c0 Heq0.
         rewrite add_carry_neg_f_r in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry_neg_t: forall a, (add_list_ingr a (map negb a) true) = mk_list_false (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry a (negb a) true); intros r0 c0 Heq0.
         rewrite add_carry_neg_t in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry: forall a, add_list_ingr a (twos_complement a) false = mk_list_false (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - unfold twos_complement. rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
         rewrite add_list_carry_empty_neutral_r.
         rewrite add_neg_list_carry_neg_t. reflexivity.
Qed.

Lemma add_neg_list_absorb: forall a, add_list a (twos_complement a) = mk_list_false (length a).
Proof. intro a. unfold add_list. rewrite add_neg_list_carry. reflexivity. Qed.

Lemma subt'_add_list: forall (a b : bitvector) (n : N), 
  N.of_nat (length a) = n -> 
  N.of_nat (length b) = n -> 
  subst_list' (add_list_ingr a b false) b = a.
Proof. intros.
  unfold subst_list', twos_complement, add_list.
  rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
  rewrite add_list_carry_empty_neutral_r.
  specialize (@add_list_carry_assoc a b (map negb b) false true false true).
  intro H2. rewrite H2; try auto. rewrite add_neg_list_carry_neg_f.
  assert (length b = length a).
    { rewrite <- H in H0. now apply Nat2N.inj in H0. }
  rewrite H1.
  now rewrite add_list_carry_unit_t.
Qed.

(* bitvector ADD-NEG properties *)

Lemma bv_add_neg_unit: forall a, bv_add a (bv_not a) = mk_list_true (nat_of_N (size a)).
Proof. intro a. unfold bv_add, bv_not, size, bits. rewrite not_list_length.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold add_list. rewrite add_neg_list_carry_neg_f.
       rewrite Nat2N.id, not_list_length. reflexivity.
Qed. 


(* bitwise ADD-SUBST properties *)

Lemma add_subst_list_carry_opp: forall n a b, (length a) = n -> (length b) = n -> (add_list_ingr (subst_list' a b) b false) = a.
Proof. intros n a b H0 H1.
       unfold subst_list', twos_complement, add_list.
       rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
       rewrite add_list_carry_empty_neutral_r.
       specialize (@add_list_carry_assoc a (map negb b) b true false false true).
       intro H2. rewrite H2; try auto. rewrite add_neg_list_carry_neg_f_r.
       rewrite H1. rewrite <- H0. rewrite add_list_carry_unit_t; reflexivity.
Qed.

Lemma add_subst_opp:  forall n a b, (length a) = n -> (length b) = n -> (add_list (subst_list' a b) b) = a.
Proof. intros n a b H0 H1. unfold add_list, size, bits.
       apply (@add_subst_list_carry_opp n a b); easy.
Qed.

(* bitvector ADD-SUBT properties *)

Lemma bv_add_subst_opp:  forall n a b, (size a) = n -> (size b) = n -> (bv_add (bv_subt' a b) b) = a.
Proof. intros n a b H0 H1. unfold bv_add, bv_subt', add_list, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@subst_list'_length a b). rewrite H0.
       rewrite N.compare_refl. rewrite (@add_subst_list_carry_opp (nat_of_N n) a b); auto;
       inversion H0; rewrite Nat2N.id; auto.
       symmetry. now rewrite <- Nat2N.inj_iff, H0.
        now rewrite <- Nat2N.inj_iff, H0.
Qed.

(* a + b - b = a *)
Lemma bv_subt'_add:  forall n a b, 
  (size a) = n -> (size b) = n -> (bv_subt' (bv_add a b) b) = a.
Proof. intros n a b H0 H1. unfold bv_add, bv_subt', add_list, size, bits in *.
  rewrite H0, H1.
  rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
  rewrite <- add_list_carry_length_eq, H0.
  rewrite N.compare_refl.
  apply (@subt'_add_list a b n); easy.
  rewrite <- H0 in H1. now apply Nat2N.inj in H1.
Qed.

 (* bitvector MULT properties *) 

Lemma prop_mult_bool_step_k_h_len: forall a b c k,
length (mult_bool_step_k_h a b c k) = length a.
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. simpl. easy.
       - intros.
         case b in *. simpl. rewrite IHa. simpl. omega.
         simpl. case (k - 1 <? 0)%Z; simpl; now rewrite IHa.
Qed. 


Lemma empty_list_length: forall {A: Type} (a: list A), (length a = 0)%nat <-> a = [].
Proof. intros A a.
       induction a; split; intros; auto; contradict H; easy.
Qed.

Lemma prop_mult_bool_step: forall k' a b res k, 
                       length (mult_bool_step a b res k k') = (length res)%nat.
Proof. intro k'.
       induction k'.
       - intros. simpl. rewrite prop_mult_bool_step_k_h_len. simpl. omega.
       - intros. simpl. rewrite IHk'. rewrite prop_mult_bool_step_k_h_len. simpl; omega.
Qed.

Lemma and_with_bool_len: forall a b, length (and_with_bool a (nth 0 b false)) = length a.
Proof. intro a.
       - induction a.
         intros. now simpl.
         intros. simpl. now rewrite IHa.
Qed.

Lemma bv_mult_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_mult a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_mult, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold mult_list, bvmult_bool.
       case_eq (length a).
         intros.
         + rewrite empty_list_length in H. rewrite H in *. now simpl in *.
         + intros.
           case n0 in *. now rewrite and_with_bool_len.
           rewrite prop_mult_bool_step. now rewrite and_with_bool_len.
Qed.

 (** list extraction *)
  Fixpoint extract (x: list bool) (i j: nat) : list bool :=
    match x with
      | [] => []
      | bx :: x' => 
      match i with
        | O      =>
        match j with
          | O    => []
          | S j' => bx :: extract x' i j'
        end
        | S i'   => 
        match j with
          | O    => []
          | S j' => extract x' i' j'
        end
     end
   end.

  Lemma zero_false: forall p, ~ 0 >= Npos p.
  Proof. intro p. induction p; lia. Qed.

  Lemma min_distr: forall i j: N, N.to_nat (j - i) = ((N.to_nat j) - (N.to_nat i))%nat.
  Proof. intros i j; case i; case j in *; try intros; lia. Qed. 

  Lemma posSn: forall n, (Pos.to_nat (Pos.of_succ_nat n)) = S n.
  Proof. intros; case n; [easy | intros; lia ]. Qed.

  Lemma _length_extract: forall a (i j: N) (H0: (N.of_nat (length a)) >= j) (H1: j >= i), 
                         length (extract a 0 (N.to_nat j)) = (N.to_nat j).
  Proof. intro a.
         induction a as [ | xa xsa IHa ].
         - simpl. case i in *. case j in *.
           easy. lia.
           case j in *; lia.
         - intros. simpl.
           case_eq j. intros.
           now simpl.
           intros. rewrite <- H.
           case_eq (N.to_nat j).
           easy. intros. simpl.
           apply f_equal.
           specialize (@IHa 0%N (N.of_nat n)).
           rewrite Nat2N.id in IHa.
           apply IHa.
           apply (f_equal (N.of_nat)) in H2.
           rewrite N2Nat.id in H2.
           rewrite H2 in H0. simpl in *. lia.
           lia.
  Qed.

  Lemma length_extract: forall a (i j: N) (H0: (N.of_nat (length a)) >= j) (H1: j >= i), 
                        length (extract a (N.to_nat i) (N.to_nat j)) = (N.to_nat (j - i)).
  Proof. intro a.
       induction a as [ | xa xsa IHa].
       - intros. simpl.
         case i in *. case j in *.
         easy. simpl in *.
         contradict H0. apply zero_false.
         case j in *. now simpl.
         apply zero_false in H0; now contradict H0.
       - intros. simpl.     
         case_eq (N.to_nat i). intros.
         case_eq (N.to_nat j). intros.
         rewrite min_distr. now rewrite H, H2.
         intros. simpl.
         rewrite min_distr. rewrite H, H2.
         simpl. apply f_equal.

         specialize (@IHa 0%N (N.of_nat n)).
         rewrite Nat2N.id in IHa.
         simpl in *.
         rewrite IHa. lia.
         lia. lia.
         intros.
         case_eq (N.to_nat j).
         simpl. intros.
         rewrite min_distr. rewrite H, H2. now simpl.
         intros.
         rewrite min_distr. rewrite H, H2.
         simpl.
         specialize (@IHa (N.of_nat n) (N.of_nat n0)).
         rewrite !Nat2N.id in IHa.
         rewrite IHa. lia.
         apply (f_equal (N.of_nat)) in H2.
         rewrite N2Nat.id in H2.
         rewrite H2 in H0. simpl in H0. lia.
         lia.
Qed.

  (** bit-vector extraction *)
  Definition bv_extr (i n0 n1: N) a : bitvector :=
    if (N.ltb n1 (n0 + i)) then mk_list_false (nat_of_N n0)
    else  extract a (nat_of_N i) (nat_of_N (n0 + i)).

  Lemma not_ltb: forall (n0 n1 i: N), (n1 <? n0 + i)%N = false -> n1 >= n0 + i.
  Proof. intro n0.
         induction n0.
         intros. simpl in *.
         apply N.ltb_nlt in H.
         apply N.nlt_ge in H. lia.
         intros. simpl.
         case_eq i.
         intros. subst. simpl in H.
         apply N.ltb_nlt in H.
         apply N.nlt_ge in H. intros. simpl in H. lia.
         intros. subst.
         apply N.ltb_nlt in H.
         apply N.nlt_ge in H. lia.
  Qed.
         
  
  Lemma bv_extr_size: forall (i n0 n1 : N) a, 
                      size a = n1 -> size (@bv_extr i n0 n1 a) = n0%N.
  Proof. 
    intros. unfold bv_extr, size in *.
    case_eq (n1 <? n0 + i).
    intros. now rewrite length_mk_list_false, N2Nat.id.
    intros.
    specialize (@length_extract a i (n0 + i)). intros.
    assert ((n0 + i - i) = n0)%N.
    { lia. } rewrite H2 in H1.
    rewrite H1.
      now rewrite N2Nat.id.
      rewrite H.
      now apply not_ltb.
      lia.
  Qed.

Lemma extract_app: forall (a b: list bool), extract (a ++ b) 0 (length a) = a.
Proof. intro a.
       induction a; intros.
       - cbn. case_eq b; intros.
         + now cbn.
         + now cbn.
       - cbn. now rewrite (IHa b).
Qed. 

Lemma extract_all: forall (a: list bool), extract a 0 (length a) = a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. now rewrite IHa at 1.
Qed. 

Lemma extract_app_all: forall (a b: list bool),
extract a 0 (length b) ++ extract a (length b) (length a) = a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq b; intros.
         cbn. now rewrite (extract_all a0).
         cbn. f_equal. now rewrite IHa.
Qed.

 (*
  Definition bv_extr (n i j: N) {H0: n >= j} {H1: j >= i} {a: bitvector} : bitvector :=
    extract a (nat_of_N i) (nat_of_N j).


  Lemma bv_extr_size: forall n (i j: N) a (H0: n >= j) (H1: j >= i), 
                      size a = n -> size (@bv_extr n i j H0 H1 a) = (j - i)%N.
  Proof. 
    intros. unfold bv_extr, size in *.
    rewrite <- N2Nat.id. apply f_equal.
    rewrite <- H in H0. 
    specialize (@length_extract a i j H0 H1); intros; apply H2.
  Qed.
 *)

  (** list extension *)
  Fixpoint extend (x: list bool) (i: nat) (b: bool) {struct i}: list bool :=
    match i with
      | O => x
      | S i' =>  b :: extend x i' b
    end.

  Definition zextend (x: list bool) (i: nat): list bool :=
    extend x i false.

  Definition sextend (x: list bool) (i: nat): list bool :=
    match x with
      | []       => mk_list_false i
      | xb :: x' => extend x i xb
    end.

  Lemma extend_size_zero: forall i b, (length (extend [] i b)) = i.
  Proof.
    intros.
    induction i as [ | xi IHi].
    - now simpl.
    - simpl. now rewrite IHi.
  Qed.

  Lemma extend_size_one: forall i a b, length (extend [a] i b) = S i.
  Proof. intros.
         induction i.
         - now simpl.
         - simpl. now rewrite IHi.
  Qed.

  Lemma length_extend: forall a i b, length (extend a i b) = ((length a) + i)%nat.
  Proof. intro a.
         induction a.
         - intros. simpl. now rewrite extend_size_zero.
         - intros.
           induction i.
           + intros. simpl. lia.
           + intros. simpl. apply f_equal.
             rewrite IHi. simpl. lia.
   Qed.

  Lemma zextend_size_zero: forall i, (length (zextend [] i)) = i.
  Proof.
    intros. unfold zextend. apply extend_size_zero. 
  Qed.

  Lemma zextend_size_one: forall i a, length (zextend [a] i) = S i.
  Proof.
    intros. unfold zextend. apply extend_size_one. 
  Qed.

  Lemma length_zextend: forall a i, length (zextend a i) = ((length a) + i)%nat.
  Proof.
     intros. unfold zextend. apply length_extend.
  Qed.

  Lemma sextend_size_zero: forall i, (length (sextend [] i)) = i.
  Proof.
    intros. unfold sextend. now rewrite length_mk_list_false.
  Qed.

  Lemma sextend_size_one: forall i a, length (sextend [a] i) = S i.
  Proof.
    intros. unfold sextend. apply extend_size_one. 
  Qed.

  Lemma length_sextend: forall a i, length (sextend a i) = ((length a) + i)%nat.
  Proof.
     intros. unfold sextend.
     case_eq a. intros. rewrite length_mk_list_false. easy.
     intros. apply length_extend.
  Qed.

  (** bit-vector extension *)
  Definition bv_zextn (n i: N) (a: bitvector): bitvector :=
    zextend a (nat_of_N i).

  Definition bv_sextn (n i: N) (a: bitvector): bitvector :=
    sextend a (nat_of_N i).

  Lemma plus_distr: forall i j: N, N.to_nat (j + i) = ((N.to_nat j) + (N.to_nat i))%nat.
  Proof. intros i j; case i; case j in *; try intros; lia. Qed. 
 
  Lemma bv_zextn_size: forall n (i: N) a, 
                      size a = n -> size (@bv_zextn n i a) = (i + n)%N.
  Proof.
    intros. unfold bv_zextn, zextend, size in *.
    rewrite <- N2Nat.id. apply f_equal. 
    specialize (@length_extend a (nat_of_N i) false). intros.
    rewrite H0. rewrite plus_distr. rewrite plus_comm.
    apply f_equal.
    apply (f_equal (N.to_nat)) in H.
    now rewrite Nat2N.id in H.
  Qed.

  Lemma bv_sextn_size: forall n (i: N) a, 
                      size a = n -> size (@bv_sextn n i a) = (i + n)%N.
  Proof.
    intros. unfold bv_sextn, sextend, size in *.
    rewrite <- N2Nat.id. apply f_equal.
    case_eq a.
    intros. rewrite length_mk_list_false.
    rewrite H0 in H. simpl in H. rewrite <- H.
    lia.
    intros.
    specialize (@length_extend a (nat_of_N i) b). intros.
    subst. rewrite plus_distr. rewrite plus_comm.
    rewrite Nat2N.id.
    now rewrite <- H1.
  Qed.



(* BV Shift Operations *)


(*BV -> Nat Conversion *)

Fixpoint pow2 (n: nat): nat :=
  match n with
    | O => 1%nat
    | S n' => (2 * pow2 n')%nat
  end.

Fixpoint _list2nat_be (a: list bool) (n i: nat) : nat :=
  match a with
    | [] => n
    | xa :: xsa =>
        if xa then _list2nat_be xsa (n + (pow2 i)) (i + 1)
        else _list2nat_be xsa n (i + 1)
  end.  

Fixpoint list2N (a: list bool) (p: N) :=
  match a with
    | []  => 0
    | x ::  xs => if x then N.succ_double (list2N xs p) else N.double (list2N xs p)
  end.

Definition list2nat_be_a (a: list bool) := N.to_nat (list2N a 0).

Definition list2nat_be (a: list bool) := _list2nat_be a 0 0.

Definition bv2nat (a: list bool) := list2nat_be a.

Definition bv2nat_a (a: list bool) := list2nat_be_a a.

(*Nat -> BV Conversion *)

(* BE: that seems incorrect?
   To test if the function works as expected, please
   run "Eval compute in fun_name args."

 Fixpoint nat2bv_aux (n : nat) (acc : list bool) :=
  match n with
  | O => acc
  | S n' => match ((N.of_nat n) mod 2) with
            | 0 => nat2bv_aux n' (acc ++ [true])
            | _ => nat2bv_aux n' (acc ++ [false])
            end
  end.

Fixpoint pad (bv : list bool) (diff : nat) :=
  match diff with
  | O => bv
  | S n => pad (bv ++ [false]) n
  end.

Definition pad_to (size : nat) (bv : list bool) : list bool :=
  pad bv (size - (length bv)).

Definition nat2bv (n : nat) (size : nat) : bitvector :=
  pad_to size (nat2bv_aux n nil).
 *)


Fixpoint pos2list (n: positive) acc :=
  match n with
    | xI m => pos2list m (acc ++ [true])
    | xO m => pos2list m (acc ++ [false])
    | xH => (acc ++ [true])
  end.

Lemma pos2list_acc: forall p a, (pos2list p a) = a ++ (pos2list p []).
Proof. intro p.
       induction p; intros.
       - cbn. rewrite IHp. specialize (IHp [true]).
         rewrite IHp. now rewrite app_assoc.
       - cbn. rewrite IHp. specialize (IHp [false]).
         rewrite IHp. now rewrite app_assoc.
       - now cbn.
Qed.

Lemma length_pos2list_acc: forall p a, (length (pos2list p a)) = (length a  + length (pos2list p []))%nat.
Proof. intros p a.
       now rewrite pos2list_acc, app_length.
Qed.

Lemma length_pos2list_nil: forall p, 
length (pos2list p []) = Pos.to_nat (Pos.size p).
Proof. intro p.
       induction p; intros.
       - cbn. rewrite length_pos2list_acc.
         cbn. rewrite IHp. admit.
(*          Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty. *)
       - cbn. rewrite length_pos2list_acc. cbn. rewrite IHp. admit.
(*          Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty. *)
       - now cbn.
Admitted.

Lemma length_pos2list: forall p a, 
  (length (pos2list p a)) = (length a  + N.to_nat (N.size (Npos p)))%nat.
Proof. intros.  
       rewrite pos2list_acc, app_length.
       f_equal. rewrite length_pos2list_nil. admit.
(* 	     Reconstr.reasy (@Coq.ZArith.Znat.positive_N_nat) (@Coq.NArith.BinNatDef.N.size). *)
Admitted.

Definition N2list (n: N) s :=
  match n with 
    | N0     => mk_list_false s
    | Npos p => if (s <? (N.to_nat (N.size n)))%nat then (firstn s (pos2list p []))
                else (pos2list p []) ++ mk_list_false (s - (N.to_nat (N.size n)))
  end.

Lemma length_N2list: forall n s, length (N2list n s) = s.
Proof. intro n.
       induction n; intros.
       - cbn. now rewrite length_mk_list_false.
       - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
         + contradict H. admit.
(*          	Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.is_pos, 
            @Coq.Arith.PeanoNat.Nat.neq_0_lt_0) Reconstr.Empty.      *) 
         + case_eq ( (s <=? n)%nat); intros.
           * rewrite firstn_length. rewrite length_pos2list_nil, H.
             admit.
(*             	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.min_l,
               @Coq.Arith.PeanoNat.Nat.leb_le, @Coq.Arith.PeanoNat.Nat.succ_le_mono)
              (@Coq.Init.Nat.min, @Coq.Init.Peano.lt). *)
           * rewrite app_length, length_pos2list_nil, H, length_mk_list_false.
             admit.
(*              	Reconstr.reasy (@Coq.Arith.Minus.le_plus_minus,
                @Coq.Arith.Compare_dec.leb_complete_conv) (@Coq.Init.Peano.lt). *)
Admitted.

Definition nat2bv (n: nat) s := N2list (N.of_nat n) s.

Lemma length_nat2bv: forall n s, length (nat2bv n s) = s.
Proof. intros. unfold nat2bv.
       now rewrite length_N2list.
Qed.


Lemma N2list_S_true: forall n m,
N2list (N.succ_double n) (S m) = true :: N2list n m.
Proof. intro n.
       induction n; intros.
       - cbn. rewrite Pos2Nat.inj_1. assert ((m - 0)%nat = m) by lia. now rewrite H.
       - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
         + cbn. contradict H. admit.
(* 	         Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.neq_0_lt_0,
             @Coq.PArith.Pnat.Pos2Nat.is_pos) Reconstr.Empty. *)
         + assert ((Pos.to_nat (Pos.succ (Pos.size p))%nat = S (S n))).
           { admit. (*	Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty. *) }
           rewrite H0.
           case_eq (m <=? n)%nat; intros; rewrite pos2list_acc; now cbn.
Admitted.

Lemma N2list_S_false: forall n m,
N2list (N.double n) (S m) = false :: N2list n m.
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
         + cbn. contradict H. admit.
(* 	         Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.neq_0_lt_0,
             @Coq.PArith.Pnat.Pos2Nat.is_pos) Reconstr.Empty. *)
         + assert ((Pos.to_nat (Pos.succ (Pos.size p))%nat = S (S n))).
           { admit. (*	Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_succ) Reconstr.Empty. *) }
           rewrite H0.
           case_eq (m <=? n)%nat; intros; rewrite pos2list_acc; now cbn.
Admitted.

Lemma N2List_list2N: forall a, N2list (list2N a 0) (length a) = a.
Proof. intro a. 
       induction a; intros.
       - now cbn.
       - cbn in *. case_eq a; intros.
         + now rewrite N2list_S_true, IHa.
         + now rewrite N2list_S_false, IHa.
Qed.


Lemma list2N_pos2list: forall p, list2N (pos2list p []) 0 = N.pos p.
Proof. intro p.
        induction p; intros.
        - cbn. rewrite pos2list_acc. cbn. rewrite IHp.
          Reconstr.reasy Reconstr.Empty (@Coq.NArith.BinNatDef.N.succ_double).
        - cbn. rewrite pos2list_acc. cbn. rewrite IHp.
          Reconstr.reasy Reconstr.Empty (@Coq.NArith.BinNatDef.N.succ_double).
        - now cbn.
Qed.

Lemma list2N_N2List: forall a, list2N (N2list a (N.to_nat (N.size a))) 0 = a.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
          + contradict H. Reconstr.rcrush (@Coq.PArith.Pnat.Pos2Nat.is_pos,
              @Coq.Arith.PeanoNat.Nat.neq_0_lt_0) Reconstr.Empty.
          + assert ((S n <=? n)%nat = false). rewrite Nat.leb_gt.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_succ_diag_r) Reconstr.Empty.
            rewrite H0. cbn.
            assert (mk_list_false (n - n) = nil).
            { Reconstr.rsimple (@Coq.Init.Peano.plus_n_O, @Coq.Init.Peano.le_n, 
               @Coq.Arith.PeanoNat.Nat.sub_0_le) (@RAWBITVECTOR_LIST.mk_list_false).
            } now rewrite H1, app_nil_r, list2N_pos2list.
Qed.

Lemma listE: forall n, (list2N (mk_list_false n) 0) = 0.
Proof. intro n.
        induction n; intros; try now cbn.
        cbn. rewrite IHn. easy.
Qed.

Lemma pos2list_mk_list_false: forall p n,
list2N (pos2list p [] ++ mk_list_false n) 0 = N.pos p.
Proof. intro p.
        induction p; intros.
        - cbn. rewrite pos2list_acc. cbn.
          rewrite IHp. easy.
        - cbn. rewrite pos2list_acc. cbn.
          rewrite IHp. easy.
        - cbn. rewrite listE. easy.
Qed. 

Lemma list2N_N2List_s: forall a n,
 ((N.to_nat (N.size a)) <=? n)%nat = true ->
 list2N (N2list a n) 0 = a.
Proof. intro a.
        induction a; intros.
        - cbn. now rewrite listE.
        - cbn. case_eq (Pos.to_nat (Pos.size p)); intros.
          + contradict H0. Reconstr.rcrush (@Coq.PArith.Pnat.Pos2Nat.is_pos,
              @Coq.Arith.PeanoNat.Nat.neq_0_lt_0) Reconstr.Empty.
          + assert ((n <=? n0)%nat = false).
            unfold N.size in *.
            Reconstr.rsimple (@Coq.ZArith.Znat.positive_N_nat, @Coq.Arith.PeanoNat.Nat.leb_le,
            @Coq.Arith.Compare_dec.leb_correct_conv) (@Coq.Init.Peano.lt).
            now rewrite H1, pos2list_mk_list_false.
Qed.

Lemma PosSizeNPos: forall p,
(N.pos (Pos.size p) <=? N.pos p) = true.
Proof. intro p.
        induction p; intros.
        - cbn. rewrite N.leb_le in *. lia.
        - cbn. rewrite N.leb_le in *. lia.
        - now cbn.
Qed.

Lemma Nsize_lt: forall a, ((N.size a) <=? a) = true.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn in *. now rewrite PosSizeNPos.
Qed.

Lemma PosSuc: forall a, (Pos.of_succ_nat a) = Pos.of_nat (S a).
Proof. intro a. Reconstr.reasy (@Coq.PArith.BinPos.Pos.of_nat_succ)
                 Reconstr.Empty. 
Qed.

Lemma NPos_size: forall a, a <> O -> (Pos.to_nat (Pos.size (Pos.of_nat a))) =
  (N.to_nat (N.size (N.of_nat a))) .
Proof. intro a.
        induction a; intros.
        - cbn. easy.
        - cbn. case_eq a; intros.
          + now cbn.
          + rewrite Coq.PArith.BinPos.Pos.succ_of_nat. easy.
            lia.
Qed.

Lemma size_gt: forall a, ((N.to_nat (N.size (N.of_nat a)))%nat <=? a)%nat = true.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn in *. rewrite PosSuc. rewrite NPos_size.
          specialize (Nsize_lt (N.of_nat (S a))); intro HH.
          assert ( (N.to_nat (N.size (N.of_nat (S a))) <=? N.to_nat (N.of_nat (S a)))%nat = true).
        	Reconstr.rcrush (@Coq.NArith.Nnat.Nat2N.id, @Coq.NArith.Nnat.N2Nat.inj_compare,
            @Coq.NArith.BinNat.N.leb_le,
            @Coq.Arith.Compare_dec.leb_compare) 
           (@Coq.NArith.BinNat.N.le).
          rewrite Nat2N.id in H. easy.
          lia.
Qed.

Lemma list2N_N2List_eq: forall a, list2N (N2list a (N.to_nat a)) 0 = a.
Proof. intros. rewrite list2N_N2List_s. easy.
        specialize (size_gt (N.to_nat a)); intro HH.
        rewrite N2Nat.id in HH. easy.
Qed.

Lemma list2N_mk_list_false: forall n, (list2N (mk_list_false n) 0) = 0%N.
Proof. intro n.
       induction n; intros. 
       + now cbn.
       + cbn. now rewrite IHn.
Qed.

(* Shift Left *)

Definition shl_one_bit  (a: list bool) : list bool :=
   match a with
     | [] => []
     | _ => false :: removelast a 
   end.

Fixpoint shl_n_bits  (a: list bool) (n: nat): list bool :=
    match n with
      | O => a
      | S n' => shl_n_bits (shl_one_bit a) n'  
    end.

Definition shl_n_bits_a  (a: list bool) (n: nat): list bool :=
  if (n <? length a)%nat then mk_list_false n ++ firstn (length a - n) a
  else mk_list_false (length a).

Definition shl_aux  (a b: list bool): list bool :=
shl_n_bits a (list2nat_be_a b).

Definition bv_shl (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shl_aux a b
  else nil.

Definition bv_shl_a (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shl_n_bits_a a (list2nat_be_a b)
  else nil.

Lemma length_shl_one_bit : forall a, length (shl_one_bit a) = length a.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - simpl. rewrite <- IHa.
         case_eq a0; easy.
Qed.

Lemma length_shl_n_bits : forall n a, length (shl_n_bits a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - reflexivity.
       - now rewrite (IHn (shl_one_bit a)), length_shl_one_bit.
Qed.

Lemma length_shl_aux : forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (shl_aux a b)).
Proof.
    intros.
    unfold shl_aux. now rewrite length_shl_n_bits.
Qed.

Lemma bv_shl_size n a b : size a = n -> size b = n -> size (bv_shl a b) = n.
Proof.
  unfold bv_shl. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- (@length_shl_aux a b (nat_of_N n)).
  now rewrite N2Nat.id.
  now apply (f_equal (N.to_nat)) in H1; rewrite Nat2N.id in H1.
  now apply (f_equal (N.to_nat)) in H2; rewrite Nat2N.id in H2.
Qed.


Lemma length_shl_n_bits_a: forall n a, length (shl_n_bits_a a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - unfold shl_n_bits_a.
         case_eq a; intros. now cbn. 
         cbn. rewrite firstn_all. easy.
       - unfold shl_n_bits_a.         
         case_eq ( (S n <? length a)%nat); intros. cbn.
         rewrite app_length, length_mk_list_false.
         rewrite firstn_length. apply Nat.ltb_lt in H.
         assert ((Init.Nat.min (length a - S n) (length a))%nat = (length a - S n)%nat).
         {  lia. }
         rewrite H0. lia.
         now rewrite length_mk_list_false.
Qed.

(* Shift Right (Logical) *)

Definition shr_one_bit (a: list bool) : list bool :=
   match a with
     | [] => []
     | xa :: xsa => xsa ++ [false]
   end.

Definition shr_n_bits_a (a: list bool) (n: nat): list bool :=
   if (n <? length a)%nat then skipn n a ++ mk_list_false n 
   else mk_list_false (length a).

Fixpoint shr_n_bits (a: list bool) (n: nat): list bool :=
    match n with
      | O => a
      | S n' => shr_n_bits (shr_one_bit a) n'  
    end.

Definition shr_aux (a b: list bool): list bool :=
shr_n_bits a (list2nat_be_a b).

Definition shr_aux_a (a b: list bool): list bool :=
shr_n_bits_a a (list2nat_be_a b).

Definition bv_shr (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shr_aux a b
  else nil.

Definition bv_shr_a (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then shr_n_bits_a a (list2nat_be_a b)
  else nil.

Lemma length_skipn: forall n (a: list bool), length (skipn n a) = (length a - n)%nat.
Proof. intro n.
       induction n; intros.
       - cbn. now rewrite <- minus_n_O.
       - cbn. case_eq a; intros.
         now cbn.
         cbn. now rewrite <- IHn.
Qed.

Lemma help_same: forall a n,
(n <? length a)%nat = true ->
firstn (length a - n) (skipn n a ++ false :: false :: mk_list_false n) =
firstn (length a - n) (skipn n a ++ false :: mk_list_false n).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq n; intros.
         cbn. f_equal. rewrite !firstn_app, !firstn_all.
         rewrite Nat.sub_diag. now cbn.
         cbn. rewrite !firstn_app. f_equal.
         rewrite length_skipn. 
         assert ((length a0 - n0 - (length a0 - n0))%nat = 0%nat) by lia.
         rewrite H1. now cbn.
Qed.

Lemma fs: forall a n,
(n <? length a)%nat = true ->
skipn n (mk_list_false n ++ firstn (length a - n) (skipn n a ++ false :: mk_list_false n)) =
skipn n a.
Proof. intro a.
       induction a; intros.
       - cbn. now rewrite app_nil_r.
       - cbn. case_eq n; intros.
         cbn. rewrite firstn_app.
         now rewrite Nat.sub_diag, firstn_all, app_nil_r.
         cbn. specialize (IHa n0).
         rewrite help_same. apply IHa.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in H. lia.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in H. lia.
Qed.

Lemma shr_n_shl_a: forall a n,
  shr_n_bits_a (shl_n_bits_a (shr_n_bits_a a n) n) n = shr_n_bits_a a n.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - unfold shr_n_bits_a.
         case_eq ((n <? length (a :: a0))%nat); intros.
         assert ( length (shl_n_bits_a (skipn n (a :: a0) ++ mk_list_false n) n) = 
                  length  (a :: a0)).
         { rewrite length_shl_n_bits_a, app_length, length_mk_list_false, length_skipn.
           apply Nat.ltb_lt in H.
           lia.
         } 
         rewrite H0, H.
         unfold shl_n_bits_a.
         assert ((length (skipn n (a :: a0) ++ mk_list_false n) = length (a :: a0))).
         { rewrite app_length, length_skipn, length_mk_list_false.
           apply Nat.ltb_lt in H.
           lia.
         }
         rewrite H1, H. cbn.
         case_eq n; intros. cbn.
         assert (firstn (length a0) (a0 ++ []) = a0).
         { now rewrite app_nil_r, firstn_all. }
         now rewrite H3.
         cbn. f_equal. rewrite fs. easy.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in *. lia.
         assert (length (shl_n_bits_a (mk_list_false (length (a :: a0))) n) = length (a :: a0)).
         { now rewrite length_shl_n_bits_a, length_mk_list_false. } 
         now rewrite H0, H.
Qed.

Lemma skipn_all: forall (A: Type) n (l: list A), ((length l <=? n)%nat = true)-> skipn n l = [].
Proof. intros A n.
       induction n; intros.
       - cbn. assert (length l = 0%nat).
         { apply Nat.leb_le in H. lia. }
         now apply length_zero_iff_nil in H0.
       - cbn. case_eq l; intros.
         + easy.
         + apply IHn. subst. cbn in H.
         apply Nat.leb_le in H.
         apply Nat.leb_le. lia.
Qed.

(* skipn n0 (mk_list_false n0 ++ firstn (length a0 - n0) (a :: a0)) = firstn (length a0 - n0) (a :: a0)
 *)
Lemma skipn_jo: forall n (a: list bool),
skipn n (mk_list_false n ++ a) = a.
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. apply IHn.
Qed.

Lemma shl_n_shr_a: forall a n,
   shl_n_bits_a (shr_n_bits_a (shl_n_bits_a a n) n) n = shl_n_bits_a a n.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - unfold shr_n_bits_a, shl_n_bits_a.
          case_eq ((n <? length (a :: a0))%nat); intros.
          rewrite !app_length, !length_mk_list_false, !firstn_length.
          assert (Hone: Init.Nat.min (length (a :: a0) - n) (length (a :: a0))%nat =
                      (length (a :: a0) - n)%nat).
          { rewrite Min.min_l. easy.
            lia.
          }
          rewrite Hone. 
          assert (Htwo: (n + (length (a :: a0) - n))%nat = (length (a :: a0))%nat).
          { rewrite le_plus_minus_r.
            easy.
            apply Nat.ltb_lt in H. lia. 
          }
          rewrite Htwo, H.
          assert (length (skipn n (mk_list_false n ++
                   firstn (length (a :: a0) - n) (a :: a0)) ++ mk_list_false n) = length (a :: a0)).
          { rewrite skipn_jo.
            rewrite app_length, firstn_length, length_mk_list_false.
            rewrite Min.min_l, Nat.sub_add.
            easy. 
            apply Nat.ltb_lt in H. lia.
            lia.
          }
          rewrite H0, H.
          f_equal.
          rewrite firstn_app, length_skipn, app_length, length_mk_list_false.
          assert ((n + length (firstn (length (a :: a0) - n) (a :: a0)) - n)%nat = 
                  (length (a :: a0) - n)%nat).
          { rewrite firstn_length.
            rewrite Min.min_l, minus_plus. easy.
            apply Nat.ltb_lt in H. lia.
          }
          rewrite H1.
          assert ((length (a :: a0) - n - (length (a :: a0) - n))%nat = 0%nat).
          { lia. }
          rewrite H2. 
          assert (firstn 0 (mk_list_false n) = []).
          { now cbn. }
          rewrite H3, app_nil_r.
          assert ((skipn n (mk_list_false n ++ firstn (length (a :: a0) - n) (a :: a0) )) =
                  (firstn (length (a :: a0) - n) (a :: a0))).
          { cbn. case_eq n; intros.
            now cbn.
            cbn. rewrite skipn_jo. easy.
          } rewrite H4. 
          now rewrite firstn_firstn, Nat.min_id.
          now rewrite !length_mk_list_false, H, length_mk_list_false, H.
Qed.

Lemma length_shr_one_bit: forall a, length (shr_one_bit a) = length a.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - simpl. rewrite <- IHa.
         case_eq a0; easy.
Qed.

Lemma length_shr_n_bits_a: forall n a, length (shr_n_bits_a a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - unfold shr_n_bits_a.
         case_eq a; intros. now cbn. 
         cbn. rewrite app_length. f_equal. easy.
       - unfold shr_n_bits_a.
         case_eq ( (S n <? length a)%nat); intros. cbn.
         case_eq a; intros. subst. cbn in *.
         now contradict H.
         unfold shr_n_bits_a. subst.
         rewrite !app_length. cbn.
         rewrite length_mk_list_false.
         rewrite length_skipn. rewrite <- plus_n_Sm.
         f_equal. rewrite Nat.sub_add; try easy.
         apply Nat.ltb_lt in H. cbn in H.
         inversion H. rewrite H1. lia.
         lia.
         now rewrite length_mk_list_false.
Qed.

Lemma length_shr_n_bits: forall n a, length (shr_n_bits a n) = length a.
Proof. intro n.
       induction n; intros; simpl.
       - reflexivity.
       - now rewrite (IHn (shr_one_bit a)), length_shr_one_bit.
Qed.

Lemma length_shr_aux: forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (shr_aux a b)).
Proof.
    intros.
    unfold shr_aux. now rewrite length_shr_n_bits.
Qed.

Lemma bv_shr_size n a b : size a = n -> size b = n -> size (bv_shr a b) = n.
Proof.
  unfold bv_shr. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- (@length_shr_aux a b (nat_of_N n)).
  now rewrite N2Nat.id.
  now apply (f_equal (N.to_nat)) in H1; rewrite Nat2N.id in H1.
  now apply (f_equal (N.to_nat)) in H2; rewrite Nat2N.id in H2.
Qed.

Lemma shl_n_shl_one: forall n a, (shl_n_bits (shl_one_bit a) n) = shl_n_bits a (S n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma shr_n_shr_one: forall n a, (shr_n_bits (shr_one_bit a) n) = shr_n_bits a (S n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma shr_n_shr_one_comm: forall n a, (shr_n_bits (shr_one_bit a) n) = shr_one_bit (shr_n_bits a n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma shl_n_shl_one_comm: forall n a, (shl_n_bits (shl_one_bit a) n) = shl_one_bit (shl_n_bits a n).
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. now rewrite IHn.
Qed.

Lemma rl_fact: forall (a: list bool) b, removelast (a ++ [b]) = a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq (a0 ++ [b]); intros.
         contradict H.
         case_eq a0; intros; subst; easy.
         now rewrite <- H, IHa.
Qed.

Lemma shl_one_b: forall a b, (shl_one_bit (a ++ [b])) = false :: a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. case_eq (a0 ++ [b]); intros.
         contradict H.
         case_eq a0; intros; subst; easy.
         rewrite <- H. f_equal. f_equal. apply rl_fact.
Qed. 

Lemma shr_one_shl: forall a, shr_one_bit (shl_one_bit (shr_one_bit a)) = shr_one_bit a.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. rewrite shl_one_b. now cbn.
Qed.

(* Shift Right (Arithmetic) *)

Definition ashr_one_bit (a: list bool) (sign: bool) : list bool :=
   match a with
     | [] => []
     | h :: t => t ++ [sign]
   end.

Definition ashr_n_bits_a (a: list bool) (n: nat) (sign: bool): list bool :=
   if (n <? length a)%nat then 
     if (Bool.eqb sign false) then skipn n a ++ mk_list_false n 
     else skipn n a ++ mk_list_true n 
   else 
     if (Bool.eqb sign false) then mk_list_false (length a)
     else mk_list_true (length a).

Fixpoint ashr_n_bits (a: list bool) (n: nat) (sign: bool): list bool :=
    match n with
      | O => a
      | S n' => ashr_n_bits (ashr_one_bit a sign) n' sign
    end.

Definition ashr_aux_a (a b: list bool): list bool :=
ashr_n_bits_a a (list2nat_be_a b) (last a false).

Definition ashr_aux (a b: list bool): list bool :=
ashr_n_bits a (list2nat_be_a b) (last a false).

Definition bv_ashr_a (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then ashr_aux_a a b
  else nil.

Definition bv_ashr (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then ashr_aux a b
  else nil.

Lemma length_ashr_one_bit: forall a sign, length (ashr_one_bit a sign) = length a.
Proof. intro a. destruct sign.
  + induction a; intros.
    - now simpl.
    - simpl. rewrite <- IHa.
      case_eq a0; easy.
  + induction a; intros.
   - now simpl.
   - simpl. rewrite <- IHa.
     case_eq a0; easy.
  Qed.

Lemma length_ashr_n_bits: forall n a sign, length (ashr_n_bits a n sign) = length a.
Proof.
  intros n.
  induction n; intros; simpl.
  - reflexivity.
  - now rewrite (IHn (ashr_one_bit a sign)), length_ashr_one_bit.
Qed. 

Lemma length_ashr_n_bits_a: forall a n sign, length (ashr_n_bits_a a n sign) = length a.
Proof. intro n.
        induction n; intros.
        - cbn.
           Reconstr.reasy (@RAWBITVECTOR_LIST.length_mk_list_false) (@RAWBITVECTOR_LIST.mk_list_false).
        - cbn. unfold ashr_n_bits_a. cbn.
           case_eq ((n0 <=? length n)%nat); intros.
           + case_eq (eqb sign false); intros.
             rewrite app_length ,length_mk_list_false.
             rewrite length_skipn.
             Reconstr.reasy (@Coq.Arith.Compare_dec.leb_correct_conv, 
              @Coq.Arith.PeanoNat.Nat.sub_add, @Coq.Arith.PeanoNat.Nat.ltb_lt, 
              @Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.ltb_ge) 
             (@RAWBITVECTOR_LIST.shl_n_bits_a, @Coq.Init.Datatypes.length, @Coq.Init.Peano.lt).
             rewrite app_length ,length_mk_list_true.
             rewrite length_skipn.
             Reconstr.reasy (@Coq.Arith.Compare_dec.leb_correct_conv, 
              @Coq.Arith.PeanoNat.Nat.sub_add, @Coq.Arith.PeanoNat.Nat.ltb_lt, 
              @Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.ltb_ge) 
             (@RAWBITVECTOR_LIST.shl_n_bits_a, @Coq.Init.Datatypes.length, @Coq.Init.Peano.lt).
           + case_eq (eqb sign false); intros.
             cbn. now rewrite length_mk_list_false.
             cbn. now rewrite length_mk_list_true.
Qed.

Lemma length_ashr_aux_a: forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (ashr_aux_a a b)).
Proof. intros.
        unfold ashr_aux_a. now rewrite length_ashr_n_bits_a.
Qed.

Lemma length_ashr_aux: forall a b n, n = (length a) -> n = (length b)%nat -> 
                     n = (length (ashr_aux a b)).
Proof.
  intros.
  unfold ashr_aux. now rewrite length_ashr_n_bits.
Qed.

Lemma bv_ashr_size n a b : size a = n -> size b = n -> size (bv_ashr a b) = n.
Proof.
  unfold bv_ashr. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- (@length_ashr_aux a b (nat_of_N n)).
  now rewrite N2Nat.id. 
  now apply (f_equal (N.to_nat)) in H1; rewrite Nat2N.id in H1.
  now apply (f_equal (N.to_nat)) in H2; rewrite Nat2N.id in H2.
  Qed.

Lemma ashr_shr_false: forall a n, ashr_n_bits_a a n false = shr_n_bits_a a n.
Proof. intro a.
       induction a; intros.
       - now cbn.
       - unfold ashr_n_bits_a, shr_n_bits_a. cbn.
         case_eq ((n <=? length a0)%nat); intros; easy.
Qed.

Lemma ashr_n_shl_a: forall a n b,
   ashr_n_bits_a (shl_n_bits_a (ashr_n_bits_a a n b) n) n b =
   ashr_n_bits_a a n b.
Proof. intros.
       case_eq b; intros.
       - revert n.
         induction a; intros.
         + now cbn.
         + unfold ashr_n_bits_a, shl_n_bits_a.
           case_eq ( (n <? length (a :: a0))%nat); intros.
           * cbn. rewrite !app_length, !length_mk_list_true.
             rewrite !length_skipn.
             assert (Hone: ((length (a :: a0) - n + n))%nat = (length (a :: a0))%nat).
             { apply Nat.ltb_lt in H0.
               Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_le_incl, 
                 @Coq.Arith.PeanoNat.Nat.sub_add) Reconstr.Empty.
             } rewrite Hone. cbn.
             assert (Htwo: (n <=? length a0)%nat = true).
             { Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_antisym, 
                  @Coq.Arith.PeanoNat.Nat.leb_nle, @Coq.Arith.PeanoNat.Nat.ltb_antisym, 
                  @Coq.Bool.Bool.negb_true_iff, @Coq.Arith.Compare_dec.leb_correct) 
                 (@Coq.Init.Nat.ltb, @Coq.Init.Datatypes.length).
             } rewrite Htwo. rewrite !app_length, !length_mk_list_false, !firstn_length.
               case_eq n; intros. cbn.
               Reconstr.reasy (@Coq.Lists.List.firstn_all, 
                  @Coq.Lists.List.app_nil_r) Reconstr.Empty.
               subst. cbn. rewrite !app_length. cbn. rewrite !length_mk_list_true.
               rewrite Min.min_l.
               assert ((n0 + (length a0 - n0))%nat = (length a0)).
               { rewrite le_plus_minus_r. easy.
                 apply Nat.leb_le in Htwo.
                 Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_le_incl) (@Coq.Init.Peano.lt).
               }
               rewrite H. case_eq a0; intros.
               subst. cbn in *. easy.
               subst. cbn in *. rewrite H0.
               case_eq n0; intros. cbn. 
               Reconstr.rcrush (@Coq.Lists.List.app_nil_r, @Coq.Lists.List.firstn_all, 
                  @Coq.Arith.PeanoNat.Nat.sub_diag, @Coq.Lists.List.app_comm_cons, 
                  @Coq.Lists.List.firstn_app) (@Coq.Lists.List.firstn).
               cbn. rewrite skipn_jo.
               rewrite firstn_app, length_skipn.
               assert (firstn (length l - n) (skipn n l) = skipn n l).
               { Reconstr.rsimple (@Coq.Lists.List.firstn_all2, 
                   @Coq.Arith.PeanoNat.Nat.lt_eq_cases,
                   @RAWBITVECTOR_LIST.length_skipn) Reconstr.Empty.
               } rewrite H2.
               assert (((length l - n - (length l - n)))%nat = O).
               { Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_diag) Reconstr.Empty. }
               rewrite H3. cbn. now rewrite app_nil_r.
               Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.le_add_r, 
                 @RAWBITVECTOR_LIST.length_skipn) Reconstr.Empty.
           * cbn. rewrite length_mk_list_true.
             assert ((n <=? length a0)%nat = false).
             { 	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_ge,
                  @Coq.Arith.PeanoNat.Nat.leb_gt) 
                 (@Coq.Init.Peano.lt, @Coq.Init.Datatypes.length).
             } rewrite H1. cbn. now rewrite length_mk_list_false, H1.
       - now rewrite !ashr_shr_false, shr_n_shl_a.
Qed.

Lemma skip_n_one_bit: forall n l b,
((n <? length (b :: l))%nat = true) ->
shr_one_bit (skipn n (b :: l)) =  skipn n l ++ [false].
Proof. intro n.
       induction n; intros.
       - now cbn.
       - cbn. case_eq l; intros. subst. cbn in *.
         now contradict H.
         rewrite <- (IHn l0 b0). easy.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in *. lia.
Qed.

Lemma mk_list_false_cons: forall n,
mk_list_false n ++ [false] = false :: mk_list_false n.
Proof. intro n.
       induction n; intros.
       now cbn.
       cbn. now rewrite <- IHn.
Qed.

Lemma shr_one_bit_append_false: forall a n,
shr_one_bit (a ++ (mk_list_false n)) = (shr_one_bit a) ++ (mk_list_false n).
Proof. intro a.
       induction a; intros.
       - cbn. case_eq n; intros.
         now cbn. cbn. now rewrite mk_list_false_cons.
       - cbn. rewrite !app_assoc_reverse.
         assert (mk_list_false n ++ [false] = [false] ++ mk_list_false n).
         { cbn. induction n; intros.
           now cbn. cbn.
           now rewrite <- IHn.
         } now rewrite H. 
Qed.

Lemma shr_one_bit_skipn_false1: forall n a,
length a = S n -> shr_one_bit (skipn n a) = [false].
Proof. intro n.
       induction n; intros.
       - cbn. case_eq a; intros. subst.
         now contradict H.
         cbn. assert (l = nil).
         subst. cbn in *. inversion H.
         apply length_zero_iff_nil in H1.
         now subst. 
         now rewrite H1, app_nil_l.
       - cbn. case_eq a; intros.
         subst. now contradict H.
         apply IHn. subst. cbn in H. lia.
Qed.

Lemma shr_one_bit_skipn_false: forall n a,
length a = S n ->
shr_one_bit (skipn n a ++ mk_list_false n) = mk_list_false n ++ [false].
Proof. intro n.
       induction n; intros.
       - cbn. rewrite app_nil_r. case_eq a; intros.
         subst. now contradict H.
         subst. cbn in *. inversion H.
         apply length_zero_iff_nil in H1.
         subst. now rewrite app_nil_l. 
       - cbn. case_eq a; intros.
         subst. now contradict H.
         rewrite <- (IHn l).
         rewrite shr_one_bit_append_false.
         assert (false :: mk_list_false n = mk_list_false (S n)).
         { easy. }
         rewrite H1, shr_one_bit_append_false.
         cbn. rewrite shr_one_bit_skipn_false1. easy.
         subst. cbn in *. lia.
         subst. cbn in *. lia.
Qed.

Lemma shr_one_bit_all_false: forall (a: list bool),
shr_one_bit (mk_list_false (length a)) = mk_list_false (length a).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - cbn. now rewrite mk_list_false_cons.
Qed.

Theorem bv_shr_aux_eq: forall n a, shr_n_bits a n = shr_n_bits_a a n.
Proof. intro n.
       induction n; intros.
       - cbn. case_eq a; intros. now cbn.
         cbn. now rewrite app_nil_r.
       - cbn. rewrite shr_n_shr_one_comm, IHn.
         unfold shr_n_bits_a.
         case_eq ((S n <? length a)%nat); intros.
         assert ((n <? length a)%nat = true).
         { apply Nat.ltb_lt in H.
           apply Nat.ltb_lt. lia.
         }
         rewrite H0. cbn. case_eq a; intros.
         subst. cbn in *. now contradict H.
         cbn.
         assert (skipn n l ++ false :: mk_list_false n = skipn n l ++ [false] ++ mk_list_false n).
         { easy. }
         rewrite H2.
         rewrite app_assoc.
         specialize (@skip_n_one_bit n l b); intros.
         rewrite <- H3.
         rewrite shr_one_bit_append_false. easy.
         apply Nat.ltb_lt in H.
         apply Nat.ltb_lt. subst. cbn in *. lia.
         case_eq ((n <? length a)%nat); intros.
         assert (length a = S n).
         { apply Nat.ltb_lt in H0.
           apply Nat.ltb_ge in H.
           lia.
         } rewrite H1, shr_one_bit_skipn_false; try easy.
         cbn. 
         now rewrite mk_list_false_cons.
         now rewrite shr_one_bit_all_false.
Qed.

Theorem bv_shr_eq: forall (a b : bitvector),
  bv_shr a b = bv_shr_a a b.
Proof. intros.
       unfold bv_shr, bv_shr_a.
       case_eq (size a =? size b); intros; try easy.
       unfold shr_aux. now rewrite bv_shr_aux_eq.
Qed.

Lemma shl_one: forall a, a <> nil -> shl_one_bit a = false :: removelast a.
Proof. intros. unfold shl_one_bit.
       induction a; intros.
       - now contradict H.
       - easy.
Qed.

Lemma shl_one_bit_app: forall a b,
  b <> nil ->
  shl_one_bit (a ++ b) = false :: a ++ removelast b.
Proof. intro a.
       induction a; intros.
       - cbn. rewrite shl_one; easy.
       - cbn. case_eq a0; case_eq b; intros.
         subst. now contradict H.
         subst. rewrite !app_nil_l. easy.
         subst. now contradict H.
         subst. rewrite <- app_comm_cons.
         f_equal. f_equal.
         rewrite <- removelast_app. easy. easy.
Qed.

Lemma removelast_one: forall (a: list bool),
 removelast (firstn 1 a) = nil.
Proof. intro a.
       induction a; intros; now cbn.
Qed.

Lemma shl_one_bit_all_false: forall (a: list bool),
shl_one_bit (mk_list_false (length a)) = mk_list_false (length a).
Proof. intro a.
       induction a; intros.
       - now cbn.
       - 
(*          cbn in *. hammer. Reconstr.reasy Reconstr.Empty Reconstr.Empty. *)
Admitted.

Lemma firstn_neq_nil: forall n (a: list bool),
a <> nil -> (n%nat <> 0%nat) -> firstn n a <> [].
Proof. intro n.
       induction n; intros.
       - cbn in *. easy.
       - admit.
(*        - Reconstr.reasy Reconstr.Empty (@Coq.Lists.List.firstn). *)
Admitted.

Theorem bv_shl_aux_eq: forall n a, shl_n_bits a n = shl_n_bits_a a n.
Proof. intro n.
       induction n; intros.
       - cbn. case_eq a; intros. now cbn.
         cbn. now rewrite firstn_all.
       - cbn. rewrite shl_n_shl_one_comm, IHn.
         unfold shl_n_bits_a.
         case_eq ((S n <? length a)%nat); intros.
         assert ((n <? length a)%nat = true).
         { apply Nat.ltb_lt in H.
           apply Nat.ltb_lt. lia.
         }
         rewrite H0. cbn. case_eq a; intros.
         subst. cbn in *. now contradict H.
         rewrite shl_one_bit_app.
         f_equal. f_equal.
         set (m := (length (b :: l) - S n)%nat).
         assert (((length (b :: l) - n)%nat = (S m)%nat)).
         { unfold m in *.
           case_eq n; intros. cbn. now rewrite Nat.sub_0_r.
           cbn.
(*            Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.ltb_lt,
           @Coq.Arith.PeanoNat.Nat.sub_succ, @Coq.Init.Peano.le_S_n,
           @Coq.Arith.Minus.minus_Sn_m) (@Coq.Init.Peano.lt, @Coq.Init.Datatypes.length). *)
           admit.
         }
         rewrite H2, removelast_firstn. easy.
         unfold m.
(*          Reconstr.rexhaustive1 (@Coq.Arith.PeanoNat.Nat.le_sub_l) (@Coq.Init.Peano.lt, @m). *)
         admit.
         cbn. case_eq n; intros. subst; cbn in *. easy.
         subst. apply Nat.ltb_lt in H. apply Nat.ltb_lt in H0.
         apply firstn_neq_nil. easy.
(*          Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_gt,
           @Coq.Arith.PeanoNat.Nat.sub_succ) (@Coq.Init.Datatypes.length). *)
         admit.
         case_eq ((n <? length a)%nat); intros.
         assert (length a = S n).
         { apply Nat.ltb_lt in H0.
           apply Nat.ltb_ge in H.
           lia.
         } rewrite H1.
         rewrite shl_one_bit_app.
         assert ((S n - n)%nat = 1%nat) by lia.
         rewrite H2, removelast_one, app_nil_r. easy.
         apply firstn_neq_nil.
         admit.
(*          Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.length). *)
         lia.
         now rewrite shl_one_bit_all_false.
Admitted.

Lemma ult_list_be_cons_false: forall a b c,
length a = length b ->
ult_list_big_endian (c :: a) (c :: b) = false -> ult_list_big_endian a b = false.
Proof. intro a. 
       induction a; intros.
       - now cbn.
       - case_eq b; intros. subst. now contradict H.
         subst. cbn.
         case_eq a0; intros.
         subst. assert (l = nil) .
         admit.
(*          { 	Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.length). } *)
         subst.  cbn in *. admit.
(*          Reconstr.rsimple Reconstr.Empty (@Coq.Init.Datatypes.negb, 
           @Coq.Init.Datatypes.orb, @Coq.Init.Datatypes.andb, @Coq.Bool.Bool.eqb). *)
         rewrite <- H1 in *. cbn in H0.
         case_eq a0; intros.
         subst. now contradict H2.
         subst. rewrite <- H2. 
         assert ( eqb c c = true) by admit.
(*          Reconstr.reasy Reconstr.Empty (@Coq.Bool.Bool.eqb). *)
         rewrite H1 in H0. 
         assert (negb c && c = false) by 	admit.
(*           Reconstr.reasy Reconstr.Empty (@Coq.Init.Datatypes.negb, @Coq.Init.Datatypes.andb). *)
         rewrite H3 in H0. admit.
(* 	       Reconstr.rcrush (@Coq.Bool.Bool.negb_true_iff, @Coq.Bool.Bool.orb_false_iff, 
           @Coq.Bool.Bool.andb_true_l) (@Coq.Init.Datatypes.negb, @Coq.Init.Datatypes.orb, 
           @Coq.Init.Datatypes.andb, @Coq.Bool.Bool.eqb). *)
Admitted.


Lemma ult_list_big_endian_unf: forall a b c d,
ult_list_big_endian (c :: a) (d :: b) =
orb (andb (Bool.eqb c d) (ult_list_big_endian a b))
    (andb (negb c) d).
Proof. intro a.
       case_eq a; intros.
       + cbn in *. case_eq b; intros. admit.
(* 	       Reconstr.reasy (@Coq.Bool.Bool.andb_false_r) 
          (@Coq.Init.Datatypes.andb, @Coq.Bool.Bool.eqb, @Coq.Init.Datatypes.orb). *)
         admit.
(*          Reconstr.reasy Reconstr.Empty Reconstr.Empty. *)
       + cbn in *. case_eq b0; intros; easy.
Admitted.

Theorem bv_shl_eq: forall (a b : bitvector),
  bv_shl a b = bv_shl_a a b.
Proof. intros.
       unfold bv_shl, bv_shl_a.
       case_eq (size a =? size b); intros; try easy.
       unfold shl_aux.
       now rewrite bv_shl_aux_eq.
Qed.

Lemma list2N_app_true: forall a,
N.to_nat (list2N (a ++ [true]) 0) = ((N.to_nat (list2N a 0))%nat + Nat.pow 2 (length a))%nat.
Proof. intro a.
        induction a; intros.
        - cbn. Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_1) Reconstr.Empty.
        - cbn. case_eq a; intros.
          + rewrite !N2Nat.inj_succ_double, IHa. cbn.
            rewrite <- !plus_n_O.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_shuffle1) Reconstr.Empty.
          + rewrite !N2Nat.inj_double. rewrite IHa.
            cbn. rewrite <- !plus_n_O.
            Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_shuffle1) Reconstr.Empty.
Qed.

Lemma list2N_app_false: forall a,
N.to_nat (list2N (a ++ [false]) 0) = (N.to_nat (list2N a 0)).
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq a; intros.
          + rewrite !N2Nat.inj_succ_double, IHa. now cbn.
          + rewrite !N2Nat.inj_double. now rewrite IHa.
Qed.

Lemma ltb_plus: forall (a b n: nat), (a <? b)%nat = (a + n <? b + n)%nat.
Proof. intros. revert a b.
        induction n; intros.
        + now rewrite <- !plus_n_O.
        + cbn. case_eq b; intros.
          cbn. symmetry. rewrite leb_iff_conv. lia. 
          cbn. 
       	  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_succ_r,
            @Coq.Arith.PeanoNat.Nat.leb_antisym, @Coq.Arith.PeanoNat.Nat.ltb_antisym, 
            @Coq.Arith.PeanoNat.Nat.add_succ_l) (@Coq.Init.Nat.ltb).
Qed.

Lemma pow_gt: forall a,
((N.to_nat (list2N a 0))%nat <? (2 ^ length a)%nat)%nat = true.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq a; intros.
          + rewrite <- plus_n_O. 
            case_eq ((2 ^ length a0 + 2 ^ length a0)%nat); intros.
            ++ contradict H0.
               Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.pow_nonzero, 
                  @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
            ++ rewrite !N2Nat.inj_succ_double. cbn.
                case_eq n; intros.
                +++ subst. contradict H0.
                     Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_0_l, 
                        @Coq.Arith.PeanoNat.Nat.add_succ_r,
                        @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
                +++ rewrite <- plus_n_O. rewrite H1 in *.
                    assert (((S (S (N.to_nat (list2N a0 0) + N.to_nat (list2N a0 0))))%nat <=? (S (S n0))%nat)%nat = true).
                    rewrite <- H0. rewrite Nat.ltb_lt in IHa.
                    rewrite Nat.leb_le. lia.
                    rewrite Nat.leb_le in H2.
                    rewrite Nat.leb_le. 
	                  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_1_l, 
                      @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Peano.lt).
          + rewrite <- plus_n_O.
            case_eq ((2 ^ length a0 + 2 ^ length a0)%nat); intros.
            ++ contradict H0.
                Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.pow_nonzero, 
                  @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
            ++ rewrite !N2Nat.inj_double. cbn.
                case_eq n; intros.
                +++ subst. contradict H0.
                     Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_0_l, 
                        @Coq.Arith.PeanoNat.Nat.add_succ_r,
                        @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
                +++ rewrite <- plus_n_O. rewrite H1 in *.
                    assert (((S (S (N.to_nat (list2N a0 0) + N.to_nat (list2N a0 0))))%nat <=? (S (S n0))%nat)%nat = true).
                    rewrite <- H0. rewrite Nat.ltb_lt in IHa.
                    rewrite Nat.leb_le. lia.
                    rewrite Nat.leb_le in H2.
                    rewrite Nat.leb_le. 
	                  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_1_l, 
                      @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Peano.lt).
Qed.

Lemma bv_ult_nat: forall a b,
    ((length a)%nat =? (length b)%nat)%nat = true ->
    bv_ult a b = (((bv2nat_a a)%nat <? (bv2nat_a b)%nat))%nat.
Proof. intros. unfold bv_ult, size in *.
         rewrite Nat.eqb_eq in H. rewrite H, N.eqb_refl.
         unfold bv2nat_a, list2nat_be_a, ult_list.
         revert b H.
         induction a using rev_ind; intros.
         - cbn in *.
	         Reconstr.rsimple (@Coq.NArith.Nnat.Nat2N.id, @RAWBITVECTOR_LIST.list2N_mk_list_false)
             (@RAWBITVECTOR_LIST.mk_list_false, @Coq.Init.Datatypes.length, @Coq.NArith.BinNatDef.N.of_nat).
         - induction b using rev_ind; intros.
           + cbn in *. contradict H.
             Reconstr.rcrush Reconstr.Empty 
              (@Coq.Init.Datatypes.length, @Coq.Init.Datatypes.app).
           + rewrite !rev_app_distr. cbn.
             case_eq (rev a); intros.
             ++ assert (rev b = nil).
                 { rewrite !app_length in H. cbn in H.
                   assert (a = nil) by Reconstr.rsimple (@Coq.Lists.List.app_nil_r,
                             @Coq.Lists.List.rev_app_distr, @Coq.Lists.List.rev_involutive)
                             Reconstr.Empty.
                   assert (length b = O). subst. cbn in *. lia.
                   Reconstr.rcrush Reconstr.Empty (@Coq.Init.Datatypes.length).
                   }
                rewrite H1.
                assert (a = nil).
                Reconstr.reasy (@Coq.Lists.List.rev_involutive, @Coq.Lists.List.rev_app_distr, 
                  @Coq.Lists.List.app_nil_r) Reconstr.Empty.
                assert (b = nil).
                Reconstr.reasy (@Coq.Lists.List.rev_involutive, @Coq.Lists.List.rev_app_distr, 
                  @Coq.Lists.List.app_nil_r) Reconstr.Empty.
                rewrite H2, H3. cbn.
                case_eq x; case_eq x0; intros; cbn; try easy.
             ++ rewrite <- H0, IHa.
                case_eq ((N.to_nat (list2N a 0) <? N.to_nat (list2N b 0))%nat); intro HH.
                * case_eq x; case_eq x0; intros.
                  ** cbn. rewrite !list2N_app_true.
                      specialize (ltb_plus (N.to_nat (list2N a 0)) (N.to_nat (list2N b 0))
                      (2 ^ length b)); intros. rewrite H3 in HH.
                      case_eq ((N.to_nat (list2N b 0) + 2 ^ length b)%nat); intros.
                      contradict H4.
                      Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_1, 
                        @Coq.Arith.PeanoNat.Nat.pow_nonzero) (@Coq.Init.Nat.add).
                      apply Nat.ltb_lt in HH. rewrite H4 in HH.
                      assert (length a = length b). rewrite !app_length in H.
                      cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                        @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                      rewrite H5. 
                    	Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.leb_le, 
                       @Coq.Arith.PeanoNat.Nat.lt_succ_r, 
                       @Coq.PArith.Pnat.Pos2Nat.inj_1) Reconstr.Empty.
                 ** cbn. rewrite list2N_app_true, list2N_app_false.
                     case_eq (N.to_nat (list2N b 0)); intros.
                     easy. rewrite H3 in HH.
                     assert (length a = length b). rewrite !app_length in H.
                     cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                       @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                     rewrite H4.
                     specialize (pow_gt b); intro Hb.
                     rewrite H3 in Hb.
                     rewrite Nat.ltb_lt in Hb. symmetry.
                     rewrite Nat.leb_gt. lia.
                  ** cbn. rewrite list2N_app_true, list2N_app_false.
                      case_eq ((N.to_nat (list2N b 0) + 2 ^ length b)%nat); intros.
                      contradict H3.
                    	Reconstr.reasy (@Coq.PArith.Pnat.Pos2Nat.inj_1, 
                        @Coq.Arith.PeanoNat.Nat.pow_nonzero) (@Coq.Init.Nat.add).
                      symmetry. rewrite Nat.leb_le. rewrite Nat.ltb_lt in HH.
                     specialize (pow_gt a); intro Ha.
                     assert (S (N.to_nat (list2N a 0)) <= S n)%nat.
                     rewrite <- H3. rewrite Nat.ltb_lt in Ha.
                      assert (length a = length b). rewrite !app_length in H.
                      cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                        @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                     rewrite H4 in Ha. lia.
                     lia.
                  ** cbn. rewrite !list2N_app_false.
                      case_eq (N.to_nat (list2N b 0)); intros.
                      contradict HH. rewrite H3.
                      Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.ltb_lt) (@Coq.Init.Peano.lt).
                      symmetry. rewrite Nat.leb_le.
                      rewrite Nat.ltb_lt in HH.
                      Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_succ_r) Reconstr.Empty.
                * case_eq x; case_eq x0; intros.
                  ** cbn. rewrite !list2N_app_true.
                      case_eq ((N.to_nat (list2N b 0) + 2 ^ length b)%nat); intros.
                      easy.
                      symmetry. rewrite Nat.leb_gt.
                      assert ((S n < S (N.to_nat (list2N a 0) + 2 ^ length a))%nat).
                      rewrite <- H3.
                      rewrite Nat.ltb_ge in HH.
                      assert (( (N.to_nat (list2N a 0)) < S (N.to_nat (list2N a 0)))%nat).
                      lia. 
                      assert (length a = length b). rewrite !app_length in H.
                      cbn in H. Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.add_succ_r, 
                                 @Coq.Init.Peano.plus_n_O) Reconstr.Empty.
                      rewrite H5. lia. lia.
                 ** cbn. rewrite list2N_app_true, list2N_app_false.
                     case_eq (N.to_nat (list2N b 0)); intros.
                     easy. rewrite H3 in HH.
                     assert (length a = length b). rewrite !app_length in H.
                     cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                       @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                     rewrite H4.
                     specialize (pow_gt b); intro Hb.
                     rewrite H3 in Hb.
                     rewrite Nat.ltb_lt in Hb. symmetry.
                     rewrite Nat.leb_gt. lia.
                  ** cbn. rewrite list2N_app_true, list2N_app_false.
                      case_eq ((N.to_nat (list2N b 0) + 2 ^ length b)%nat); intros.
                      contradict H3.
                      specialize (pow_gt b); intro Hb. rewrite Nat.ltb_lt in Hb.
            	        Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.pow_nonzero, 
                        @Coq.PArith.Pnat.Pos2Nat.inj_1) (@Coq.Init.Nat.add).
                      symmetry. rewrite Nat.leb_le. rewrite Nat.ltb_ge in HH.
                      specialize (pow_gt a); intro Ha.
                      assert (S (N.to_nat (list2N a 0)) <= S n)%nat.
                      rewrite <- H3. rewrite Nat.ltb_lt in Ha.
                      assert (length a = length b). rewrite !app_length in H.
                      cbn in H. Reconstr.reasy (@Coq.Init.Peano.eq_add_S, 
                        @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
                      rewrite H4 in Ha. lia.
                      lia.
                  ** cbn. rewrite !list2N_app_false.
                      case_eq (N.to_nat (list2N b 0)); intros.
                      easy.
                      symmetry. rewrite Nat.leb_gt.
                      rewrite Nat.ltb_ge in HH.
                      Reconstr.reasy Reconstr.Empty (@Coq.Init.Peano.lt).
                * rewrite !app_length in H. cbn in H. 
                  Reconstr.reasy (@Coq.Init.Peano.plus_n_Sm, @Coq.Init.Peano.plus_n_O) 
                   Reconstr.Empty.
Qed.

Lemma last_mk_lits_false: forall n, last (mk_list_false n) false = false.
Proof. intro n.
        induction n; intros.
        - now cbn.
        - cbn. case_eq ( mk_list_false n ); intros.
          + easy.
          + now rewrite <- H.
Qed.

Lemma last_mk_lits_true: forall n, (n <> 0)%nat -> last (mk_list_true n) false = true.
Proof. intro n.
        induction n; intros.
        - now cbn.
        - cbn. case_eq ( mk_list_true n ); intros.
          + easy.
          + rewrite <- H0. apply IHn. 
            Reconstr.reasy Reconstr.Empty (@RAWBITVECTOR_LIST.mk_list_true).
Qed.

Lemma last_shl_zeros: forall n,
last (shl_n_bits_a (mk_list_false n) n) false = false.
Proof. intro n.
        induction n; intros.
        + now cbn.
        + cbn. unfold shl_n_bits_a. cbn.
          rewrite length_mk_list_false.
          case_eq n; intros.
          easy.
          assert ((S n0 <=? n0)%nat = false).
          rewrite Nat.leb_gt. lia.
          rewrite H0. cbn.
          case_eq (mk_list_false n0); intros.
          easy. 
          now rewrite <- H1, last_mk_lits_false.
Qed.

Lemma last_app: forall (a b: list bool) c, b <> nil -> last (a ++ b) c = last b c.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq (a0 ++ b); intros.
          + contradict H0. 
         	  Reconstr.rsimple Reconstr.Empty (@Coq.Init.Datatypes.app).
          + specialize (IHa b c). rewrite H0 in IHa.
            apply IHa. easy.
Qed.

Lemma last_fristn_skipn: forall a n,
(n <? length a)%nat = true ->
last (firstn (length a - n) (skipn n a)) false = last a false.
Proof. intro a.
        induction a; intros.
        - now cbn.
        - cbn. case_eq n; intros.
          + cbn. rewrite firstn_all.
            easy.
          + cbn. rewrite IHa.
            case_eq a0; intros.
            ++ cbn in H. subst. now contradict H.
            ++ easy.
            ++ subst.
               Reconstr.reasy (@Coq.Arith.Lt.lt_S_n, @Coq.Arith.PeanoNat.Nat.ltb_lt) (@Coq.Init.Datatypes.length).
Qed.

Lemma last_skipn_false: forall a n,
(n <? length a)%nat = true ->
last (shl_n_bits_a (skipn n a ++ mk_list_false n) n) false = last a false.
Proof. intros.
        unfold shl_n_bits_a.
        assert (length (skipn n a ++ mk_list_false n) = length a).
        rewrite app_length, length_skipn, length_mk_list_false.
        rewrite Nat.ltb_lt in H.
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_add, 
         @Coq.Arith.PeanoNat.Nat.lt_le_incl) Reconstr.Empty.
        rewrite H0, H. rewrite last_app.
        rewrite firstn_app. rewrite length_skipn.
        assert ((length a - n - (length a - n))%nat = O).
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_diag) Reconstr.Empty.
        rewrite H1. cbn. rewrite app_nil_r.
        rewrite last_fristn_skipn. easy.
        easy. rewrite Nat.ltb_lt in H. apply firstn_neq_nil.
     	  Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.leb_le, @Coq.Init.Peano.le_n,  
          @Coq.Lists.List.length_zero_iff_nil, @RAWBITVECTOR_LIST.length_mk_list_false,
          @Coq.Arith.PeanoNat.Nat.leb_gt) (@Coq.Init.Datatypes.app).
        Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_gt) Reconstr.Empty.
Qed.

Lemma last_skipn_true: forall a n,
(n <? length a)%nat = true ->
last (shl_n_bits_a (skipn n a ++ mk_list_true n) n) false = last a false.
Proof. intros.
        unfold shl_n_bits_a.
        assert (length (skipn n a ++ mk_list_true n) = length a).
        rewrite app_length, length_skipn, length_mk_list_true.
        rewrite Nat.ltb_lt in H.
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_add, 
         @Coq.Arith.PeanoNat.Nat.lt_le_incl) Reconstr.Empty.
        rewrite H0, H. rewrite last_app.
        rewrite firstn_app. rewrite length_skipn.
        assert ((length a - n - (length a - n))%nat = O).
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.sub_diag) Reconstr.Empty.
        rewrite H1. cbn. rewrite app_nil_r.
        rewrite last_fristn_skipn. easy.
        easy. rewrite Nat.ltb_lt in H. apply firstn_neq_nil.
     	  Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.leb_le, @Coq.Init.Peano.le_n,  
          @Coq.Lists.List.length_zero_iff_nil, @RAWBITVECTOR_LIST.length_mk_list_false,
          @Coq.Arith.PeanoNat.Nat.leb_gt) (@Coq.Init.Datatypes.app).
        Reconstr.rcrush (@Coq.Arith.PeanoNat.Nat.sub_gt) Reconstr.Empty.
Qed.


End RAWBITVECTOR_LIST.

Module BITVECTOR_LIST <: BITVECTOR.

  Include RAW2BITVECTOR(RAWBITVECTOR_LIST).

  Notation "x |0" := (cons false x) (left associativity, at level 73, format "x |0"): bv_scope.
  Notation "x |1" := (cons true x) (left associativity, at level 73, format "x |1"): bv_scope.
  Notation "'b|0'" := [false] (at level 70): bv_scope.
  Notation "'b|1'" := [true] (at level 70): bv_scope.
  Notation "# x |" := (@of_bits x) (no associativity, at level 1, format "# x |"): bv_scope.
  Notation "v @ p" := (bitOf p v) (at level 1, format "v @ p ") : bv_scope.

End BITVECTOR_LIST.

(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)
