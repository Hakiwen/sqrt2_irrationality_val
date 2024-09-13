Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.

Open Scope R_scope.

(* Definition of a rational number *)
Definition rational (x : R) :=
  exists p q : Z, q <> 0%Z /\ Z.gcd p q = 1%Z /\ x = (IZR p) / (IZR q).

(* Definition of an irrational number *)
Definition irrational (x : R) := ~ rational x.

(* Lemma stating that the square of an integer has the same evenness as the integer itself *)
Lemma Z_even_square : forall n : Z, Z.even (n * n) = Z.even n.
Proof.
  intros n.
  destruct (Z.even n) eqn:Heven.
  - (* Case when n is even *)
    apply Z.even_spec in Heven.
    destruct Heven as [k Hk].
    rewrite Hk.
    simpl.
    rewrite Z.mul_assoc.
    rewrite Z.mul_comm with (n := 2%Z) (m := k).
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_assoc with (n := 2%Z).
    rewrite <- Z.mul_assoc.
    apply Z.even_spec.
    exists (2 * k * k).
    ring.
  - (* Case when n is odd *)
    apply Zodd_ex in Heven.
    destruct Heven as [k Hk].
    rewrite Hk.
    simpl.
    ring_simplify.
    apply Zodd_spec.
    exists (2 * k * (k + 1)).
    ring.
Qed.

(* The main theorem stating that sqrt 2 is irrational *)
Theorem sqrt2_irrational : irrational (sqrt 2).
Proof.
  unfold irrational, rational.
  intros [p [q [Hq [Hgcd Heq]]]].
  (* Assume sqrt 2 = p / q, with gcd(p, q) = 1 *)
  assert (H1: (sqrt 2) ^ 2 = ((IZR p) / (IZR q)) ^ 2).
  { rewrite Heq. reflexivity. }
  rewrite sqrt_def in H1; [|lra].
  assert (H2: 2 = ((IZR p) / (IZR q)) ^ 2) by exact H1.
  (* Simplify the equation *)
  assert (H3: 2 = (IZR p) ^ 2 / (IZR q) ^ 2) by exact H2.
  (* Cross-multiply *)
  assert (H4: 2 * (IZR q) ^ 2 = (IZR p) ^ 2).
  {
    apply Rmult_eq_reg_r with (r := (IZR q) ^ 2); [|apply pow_nonzero; apply IZR_neq; lia].
    rewrite Rmult_assoc, Rinv_r; [|apply pow_nonzero; apply IZR_neq; lia].
    rewrite Rmult_1_r, <- H3, Rmult_comm. reflexivity.
  }
  (* Convert back to integers *)
  assert (H5: (IZR p) ^ 2 = IZR (p * p)) by (rewrite <- IZR_mult; reflexivity).
  assert (H6: (IZR q) ^ 2 = IZR (q * q)) by (rewrite <- IZR_mult; reflexivity).
  rewrite H5, H6 in H4.
  rewrite <- IZR_mult in H4.
  (* Obtain the integer equation *)
  assert (H7: IZR (2 * q * q) = IZR (p * p)) by exact H4.
  apply IZR_inj in H7.
  assert (H8: p * p = 2 * q * q) by lia.
  (* Show that p is even *)
  assert (Hp_even: Z.even p = true).
  {
    apply Z_even_square in H8.
    rewrite <- H8.
    apply Z.even_mul; simpl; reflexivity.
  }
  (* Express p as 2k *)
  destruct (Zeven_ex p) as [k Hk]; [assumption|].
  (* Substitute back into the equation *)
  rewrite Hk in H8.
  simpl in H8.
  ring_simplify in H8.
  (* Show that q is even *)
  assert (Hq_even: Z.even q = true).
  {
    apply Z_even_square in H8.
    rewrite H8.
    apply Z.even_mul; simpl; reflexivity.
  }
  (* Express q as 2l *)
  destruct (Zeven_ex q) as [l Hl]; [assumption|].
  (* Derive contradiction with gcd(p, q) = 1 *)
  rewrite Hk, Hl in Hgcd.
  assert (Hgcd_new: Z.gcd (2 * k) (2 * l) = 2 * Z.gcd k l).
  {
    apply Z.gcd_mul_mono_l.
    lia.
  }
  rewrite Hgcd_new in Hgcd.
  assert (H11: 2 * Z.gcd k l = 1%Z) by assumption.
  lia.
Qed.
