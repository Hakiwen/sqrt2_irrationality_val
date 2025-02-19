Require Import ZArith.
Require Import Znumtheory.
Open Scope Z_scope.

(*
  We prove that for all integers p and q with q nonzero and
  gcd(p, q) = 1, it is not the case that p² = 2·q².
  In other words, there is no “reduced” fraction p/q whose square is 2.
  
  The idea is the classical proof: if p² = 2·q² then p² is even.
  A known lemma (Znumtheory.Zsquare_even) shows that if n² is even then n is even.
  Thus p is even, so p = 2·k for some k.
  Substituting back, we get 4·k² = 2·q² so that q² is even,
  and hence q is even. But then both p and q are even, contradicting
  the assumption that gcd(p,q)=1.
*)

Theorem sqrt2_irrational :
  forall p q : Z, q <> 0 -> Z.gcd p q = 1 -> p * p <> 2 * q * q.
Proof.
  intros p q Hq Hcop H.
  (* From p² = 2·q² we deduce that p² is even. *)
  assert (Heven_pp: Z.even (p * p) = true).
  { rewrite H.
    (* 2*q*q is even because 2 divides it. *)
    apply Zeven_spec.
    exists (q * q); ring.
  }
  (* Use the lemma that if n² is even then n is even *)
  apply Znumtheory.Zsquare_even in Heven_pp.
  destruct Heven_pp as [k Hp_even].  (* so p = 2*k *)
  rewrite Hp_even in H.
  (* Replace in the equation: (2*k)² = 2*q² becomes 4*k² = 2*q² *)
  assert (H1: 2 * q * q = 4 * k * k) by (rewrite H; ring).
  (* Write 4*k² as 2*(2*k²) *)
  replace (4 * k * k) with (2 * (2 * k * k)) in H1 by ring.
  (* So 2*q² = 2*(2*k²) hence q² = 2*k²; in particular, q² is even *)
  assert (Heven_qq: Z.even (q * q) = true).
  { rewrite <- H1.
    apply Zeven_spec.
    exists (2 * k * k); ring.
  }
  (* Use the even-square lemma to deduce that q is even *)
  apply Znumtheory.Zsquare_even in Heven_qq.
  destruct Heven_qq as [l Hq_even].  (* so q = 2*l *)
  (* Hence 2 divides both p and q *)
  assert (Hp2: 2 | p) by (exists k; assumption).
  assert (Hq2: 2 | q) by (exists l; assumption).
  (* A standard lemma (Znumtheory.Zdivide_gcd) shows that if 2 divides p and q then
     2 divides gcd(p,q) *)
  assert (Hdiv: 2 | Z.gcd p q) by (apply Znumtheory.Zdivide_gcd; assumption).
  rewrite Hcop in Hdiv.
  simpl in Hdiv.
  discriminate.
Qed.
