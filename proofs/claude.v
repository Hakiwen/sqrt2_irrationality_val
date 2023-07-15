Require Import Reals.
Open Scope R_scope.

Theorem sqrt2_irrational : ~exists n : nat, sqrt 2 = INR n.
Proof.
  intros contra.
  destruct contra as [n H]. 
  assert (Hsqrt : sqrt 2 = INR n) by exact H.
  assert (Hsq : (INR n) * (INR n) = 2) by ring_simplify in Hsqrt.
  destruct (even_odd_dec n) as [Hn|Hn].
  - (* n is even *)
    assert (Hn_even : exists k, n = 2 * k).
    { exists (n / 2). reflexivity. }
    destruct Hn_even as [k Hk].
    subst n.
    rewrite Hk in Hsq.
    simpl in Hsq. 
    assert (Hsq_even : (2 * (INR k)) * (2 * (INR k)) = 2).
    { rewrite <- Hsq. reflexivity. }
    simpl in Hsq_even.
    apply not_even_two in Hsq_even.
    contradiction.
  - (* n is odd *)
    assert (Hn_odd : exists k, n = 2 * k + 1).
    { exists (n / 2). reflexivity. }
    destruct Hn_odd as [k Hk].
    subst n. 
    rewrite Hk in Hsq.
    simpl in Hsq.
    assert (Hsq_odd : (2 * (INR k) + 1) * (2 * (INR k) + 1) = 2).
    { rewrite <- Hsq. reflexivity. }
    simpl in Hsq_odd.
    apply not_odd_two in Hsq_odd.
    contradiction.
Qed.
