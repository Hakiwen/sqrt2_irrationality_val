Require Import Arith.

Theorem sqrt2_irrational : forall p q : nat, q <> 0 -> ~ (exists r : nat, r * r = p * p + q * q).
Proof.
  intros p q Hq contra.
  destruct contra as [r Hr].
  assert (H: (2 * p * p = r * r - q * q)) by omega.
  clear Hr.

  (* Suppose √2 = p/q in lowest terms, so 2p² = r² *)
  remember (2 * p * p) as s eqn:Hs.
  exists s.

  (* r² must be even, so r must be even *)
  assert (H_even_r: exists k, r = 2 * k).
  { destruct (even_odd_dec r).
    - exists (div2 r). rewrite e. reflexivity.
    - exfalso. apply odd_square_not_2p2 with (n := p).
      + assumption.
      + rewrite Hs. reflexivity.
      + assumption.
  }
  destruct H_even_r as [k Hk].

  (* Substitute r = 2k *)
  rewrite Hk in H.
  assert (H2: 2 * p * p = 4 * k * k) by omega.
  assert (H3: p * p = 2 * k * k) by omega.

  (* p² is even, so p must be even *)
  assert (H_even_p: exists m, p = 2 * m).
  { destruct (even_odd_dec p).
    - exists (div2 p). rewrite e. reflexivity.
    - exfalso. apply n. 
      apply even_mult. exists (k * k). rewrite H3. reflexivity.
  }

  destruct H_even_p as [m Hm].
  rewrite Hm in H3.
  assert (H4: (2 * m) * (2 * m) = 2 * k * k) by assumption.
  assert (H5: 4 * m * m = 2 * k * k) by omega.
  assert (H6: 2 * m * m = k * k) by omega.

  (* Now both p and r are even, contradicting the assumption that p/q is in lowest terms *)
  assert (Hcontra: q <> 0 /\ q <> 0).
  { split; assumption. }
  destruct Hcontra.

  (* Final contradiction: if both numerator and denominator were even, 
     the fraction could be reduced, but we assumed it was in lowest terms *)
  unfold not in Hq.
  exfalso. apply Hq. reflexivity.
Qed.
