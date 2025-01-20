Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Theorem sqrt2_irrational :
  forall a b : Z, b ≠ 0 → Z.gcd a b = 1 → a^2 = 2 * b^2 → False.
Proof.
  intros a b Hb_neq0 H_gcd H_eq.
  
  (* Show that a is even *)
  assert (H_a_even : Z.even a).
  {
    unfold Z.even.
    exists (a / 2).
    simpl.
    rewrite <- H_eq.
    reflexivity.
  }
  
  (* Let a = 2 * k for some integer k *)
  destruct H_a_even as [k H_a].
  
  (* Substitute a = 2 * k into the equation a^2 = 2 * b^2 *)
  rewrite H_a in H_eq.
  simpl in H_eq.
  rewrite Zmult_assoc in H_eq.
  rewrite Zmult_comm in H_eq.
  rewrite Zmult_assoc in H_eq.
  
  (* Simplify to get b^2 = 2 * k^2 *)
  assert (H_b_even : Z.even b).
  {
    unfold Z.even.
    exists (b / 2).
    simpl.
    rewrite <- H_eq.
    reflexivity.
  }
  
  (* Let b = 2 * m for some integer m *)
  destruct H_b_even as [m H_b].
  
  (* Now, both a and b are even, contradicting gcd(a, b) = 1 *)
  assert (H_gcd_2 : Z.gcd (2 * k) (2 * m) = 2 * Z.gcd k m).
  {
    apply Z.gcd_mul_same.
    reflexivity.
  }
  
  rewrite H_gcd_2 in H_gcd.
  rewrite Zmult_comm in H_gcd.
  rewrite Z.gcd_comm in H_gcd.
  
  (* Since gcd(a, b) = 2 * gcd(k, m) = 1, this implies 2 divides 1, which is false *)
  assert (H_divides : 2 divides 1).
  {
    apply Z.divide_eq.
    rewrite H_gcd.
    rewrite Zmult_comm.
    reflexivity.
  }
  
  (* 2 does not divide 1, leading to a contradiction *)
  apply Zdivide_abs in H_divides.
  apply Zabs_eq in H_divides.
  discriminate.
Qed.
