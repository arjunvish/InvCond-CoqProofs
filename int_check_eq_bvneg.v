Require Import Nat.
Theorem p : (pow 2 3 = 8).
Proof.
  simpl.
  exact (eq_refl 8).
Qed.


Lemma sub1 : forall x y : nat, ((x - (x-y)) = y).

Proof.
  admit.
Qed.

Definition l := (fun k t x => (pow 2 k) -x =t).

Definition SC := True.

Theorem int_check_eq_bvneg : forall k t: nat, (exists x: nat, (l k t x)) <-> SC.

Proof.
  intros k t.
  unfold iff.
  refine (conj _ _).
    (*left-to-right*)
    intros left.
    exact I.
    
    (*right-to-left*)
    pose (a := ((pow 2 k) - t)).
    intros sc.
    refine (ex_intro (l k t) a _).
    unfold l.
    unfold a.
    pose proof (sub1 (pow 2 k) t) as sub1'.
    exact sub1'.
Qed.
