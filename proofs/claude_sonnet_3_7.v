Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

(* The square root of 2 is irrational *)
Theorem sqrt2_irrational : 
  ~(exists p q : Z, q <> 0 /\ Zgcd p q = 1 /\ p * p = 2 * q * q).
Proof.
  intros [p [q [Hq [Hgcd Hsquare]]]].
  
  (* p² = 2q² implies p is even *)
  assert (Hp_even : exists k, p = 2 * k).
  { destruct (Z.even_odd_dec p) as [Heven | Hodd].
    - apply Z.even_spec in Heven. assumption.
    - (* If p is odd, we get a contradiction *)
      assert (Hp_sq_odd : Z.odd (p * p)).
      { apply Z.odd_mul_odd; assumption. }
      assert (Hp_sq_even : Z.even (p * p)).
      { rewrite Hsquare. apply Z.even_mul_l. exists 1. reflexivity. }
      assert (Hcontra : Z.odd (p * p) /\ Z.even (p * p)).
      { split; assumption. }
      contradiction Hcontra.
  }
  
  (* p = 2k for some k *)
  destruct Hp_even as [k Hp].
  
  (* Substitute p = 2k into p² = 2q² *)
  rewrite Hp in Hsquare.
  replace ((2 * k) * (2 * k)) with (4 * k * k) in Hsquare by ring.
  
  (* From 4k² = 2q², we get 2k² = q² *)
  assert (Hq2 : q * q = 2 * k * k).
  { apply Z.mul_cancel_l with (p := 2).
    - lia.
    - rewrite <- Hsquare. ring. }
  
  (* q² = 2k² implies q is even, by the same argument used for p *)
  assert (Hq_even : exists m, q = 2 * m).
  { destruct (Z.even_odd_dec q) as [Heven | Hodd].
    - apply Z.even_spec in Heven. assumption.
    - (* If q is odd, we get a contradiction *)
      assert (Hq_sq_odd : Z.odd (q * q)).
      { apply Z.odd_mul_odd; assumption. }
      assert (Hq_sq_even : Z.even (q * q)).
      { rewrite Hq2. apply Z.even_mul_l. exists 1. reflexivity. }
      assert (Hcontra : Z.odd (q * q) /\ Z.even (q * q)).
      { split; assumption. }
      contradiction Hcontra.
  }
  
  (* q = 2m for some m *)
  destruct Hq_even as [m Hq].
  
  (* If both p and q are even, then gcd(p,q) >= 2, contradicting gcd(p,q) = 1 *)
  rewrite Hp, Hq in Hgcd.
  
  assert (H2_div_gcd : 2 | Zgcd (2 * k) (2 * m)).
  { apply Zgcd_is_gcd.
    - exists k. reflexivity.
    - exists m. reflexivity. }
  
  rewrite Hgcd in H2_div_gcd.
  destruct H2_div_gcd as [g Hg].
  
  assert (H1: 2 * g = 1).
  { assumption. }
  
  assert (Hcontra: 2 * g >= 2).
  { apply Z.mul_le_mono_nonneg_l.
    - lia.
    - lia. }
  
  lia. (* Contradiction: 1 = 2 * g >= 2 *)
Qed.
