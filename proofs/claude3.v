Require Import Arith.

Theorem sqrt_2_irrational : forall p q, p^2 <> 2 * q^2.
Proof.
  intros p q.
  intro H.
  assert (H1 : p * p = 2 * q * q).
  { rewrite H. reflexivity. }
  assert (H2 : exists k, p = 2 * k \/ p = 2 * k + 1).
  { destruct p as [|p'].
    - exists 0. left. reflexivity.
    - exists (p' / 2). right. rewrite Nat.add_0_r. rewrite <- Nat.div_add_l by lia. reflexivity.
  }
  destruct H2 as [k [H3|H3]].
  - rewrite H3 in H1. rewrite <- mult_assoc in H1. rewrite Nat.mul_comm in H1. rewrite mult_assoc in H1. rewrite <- Nat.mul_assoc in H1. rewrite <- Nat.mul_add_distr_l in H1. rewrite Nat.mul_comm in H1. rewrite <- Nat.mul_add_distr_r in H1. rewrite Nat.mul_1_r in H1. rewrite Nat.mul_1_l in H1. discriminate H1.
  - rewrite H3 in H1. simpl in H1. rewrite Nat.mul_comm in H1. rewrite mult_assoc in H1. rewrite <- Nat.mul_assoc in H1. rewrite <- Nat.mul_add_distr_l in H1. rewrite Nat.mul_comm in H1. rewrite <- Nat.mul_add_distr_r in H1. rewrite Nat.mul_1_r in H1. rewrite Nat.mul_1_l in H1. discriminate H1.
Qed.
