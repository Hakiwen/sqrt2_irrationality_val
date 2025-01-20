Require Import ZArith Znumtheory.
Open Scope Z_scope.

Theorem sqrt2_irrational : ~ exists a b : Z, b <> 0 /\ a * a = 2 * (b * b) /\ Z.gcd a b = 1.
Proof.
  intro H; destruct H as (a & b & Hneq & Heq & Hgcd).
  (* Show that 2 divides a² *)
  assert (H2 : (2 | a * a)) by (exists (b * b); rewrite Heq; ring).
  (* Since 2 is prime, it divides a *)
  apply Znumtheory.prime_divisors in H2; auto using Znumtheory.prime_2.
  destruct H2 as [H2 | H2]; [ | destruct H2]; auto.
  - (* Express a as 2k *)
    destruct H2 as (k & Hk).
    rewrite Hk in Heq.
    (* Simplify the equation to 2k² = b² *)
    assert (2 * (2 * k * k) = 2 * (b * b)) by (rewrite Heq; ring).
    apply Z.mul_cancel_l in H0; [ | discriminate].
    (* Show that 2 divides b² *)
    assert (H3 : (2 | b * b)) by (exists (k * k); rewrite <- H0; ring).
    apply Znumtheory.prime_divisors in H3; auto using Znumtheory.prime_2.
    destruct H3 as [H3 | H3]; [ | destruct H3]; auto.
    + (* Express b as 2m *)
      destruct H3 as (m & Hm).
      (* 2 divides gcd(a, b), contradicting gcd(a, b) = 1 *)
      assert (2 | Z.gcd a b).
      { apply Z.gcd_greatest; auto with zarith.
        - rewrite Hk; auto with zarith.
        - rewrite Hm; auto with zarith. }
      rewrite Hgcd in H1.
      absurd (2 | 1); auto with zarith.
Qed.
