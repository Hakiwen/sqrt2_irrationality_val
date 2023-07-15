Require Import ZArith.
Require Import Znumtheory.
Require Import BinInt.

Definition square (n : Z) := n * n.

Lemma square_even : forall p : Z, (Z.even (square p)) = Z.even p.
Proof.
  intros. unfold square.
  rewrite Z.even_mul. apply orb_diag.
Qed.

Lemma square_pos : forall n : Z, 0 <= n -> 0 <= square n.
Proof.
  intros. unfold square.
  apply Z.mul_nonneg_nonneg; assumption.
Qed.

Theorem sqrt2_irrational : forall p q : Z, 0 < q -> square p = 2 * square q -> rel_prime p q -> False.
Proof.
  intros p q Hq Hrel Hcoprime.
  assert (Z.even (square p) = true).
  {
    rewrite Hrel. simpl.
    apply Z.even_2p.
  }
  rewrite square_even in H.
  apply Z.even_spec in H.
  destruct H as [p' Hp].
  assert (Z.even (square q) = true).
  {
    rewrite <- Hrel in H.
    assumption.
  }
  rewrite square_even in H0.
  apply Z.even_spec in H0.
  destruct H0 as [q' Hq'].
  assert (rel_prime p' q').
  {
    rewrite Hp in Hcoprime.
    rewrite Hq' in Hcoprime.
    apply rel_prime_mult in Hcoprime.
    destruct Hcoprime as [Hcoprime _].
    rewrite Z.gcd_even in Hcoprime.
    rewrite Hp in Hcoprime.
    apply Z.even_spec in Hcoprime.
    destruct Hcoprime as [p'' Hp''].
    rewrite Z.mul_comm in Hp''.
    apply Z.mul_reg_r in Hp''.
    rewrite Hp''.
    apply Z.rel_prime_1.
    unfold not. intro. discriminate H1.
    unfold not. intro. discriminate H1.
  }
  rewrite Hp in Hrel.
  rewrite Hq' in Hrel.
  apply Z.mul_reg_r in Hrel.
  assert (2 * p' = p).
  {
    rewrite Z.mul_comm.
    apply Hp.
  }
  assert (2 * q' = q).
  {
    rewrite Z.mul_comm.
    apply Hq'.
  }
  rewrite H1 in Hcoprime.
  rewrite H2 in Hcoprime.
  apply not_rel_prime_mult in Hcoprime.
  destruct Hcoprime.
  - apply Znumtheory.Zis_gcd_gcd in H3. simpl in H3. discriminate H3.
  - apply Znumtheory.Zis_gcd_gcd in H3. simpl in H3. discriminate H3.
  - apply Z.lt_le_incl. apply Hq.
  - unfold not. intro. discriminate H1.
  - unfold not. intro. discriminate H1.
Qed.

