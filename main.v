Require Import Lia.
From Coq Require Import Arith.Wf_nat.

Section PAXOS.

  Context {A : Type}.
  Context {P : Type}.
  Context {V : Type}.
  Context {Q : (A -> Prop) -> Prop}.

  Variable (S : (A -> nat * V -> Prop) * (P -> nat * V -> Prop)).

  Definition Accepted := fst S.
  Definition Proposed := snd S.

  Definition Chosen q nv := forall a, q a -> Accepted a nv.
  Definition Empty q n := forall a n' v', q a -> n' < n -> ~ Accepted a (n', v').
  Definition Occupied q n v :=
    exists n', n' < n
          /\ (exists a, q a /\ Accepted a (n', v))
          /\ (forall a n'' v'', q a -> n'' < n -> Accepted a (n'', v'') -> n'' <= n').

  Hypothesis NDISJ : forall q1 q2, Q q1 -> Q q2 -> exists a, q1 a /\ q2 a.
  Hypothesis INV0 : forall p1 p2 n v1 v2, Proposed p1 (n, v1) -> Proposed p2 (n, v2) -> p1 = p2 /\ v1 = v2.
  Hypothesis INV1 : forall a n v, Accepted a (n, v) -> exists p, Proposed p (n, v).
  Hypothesis INV2 : forall p n v, Proposed p (n, v) -> exists q, Q q /\ (Empty q n \/ Occupied q n v).

  Lemma quorum_nonempty q : Q q -> exists a, q a.
  Proof. firstorder. Qed.

  Lemma accept_unique a1 a2 n v1 v2
    (H1 : Accepted a1 (n, v1))
    (H2 : Accepted a2 (n, v2))
    : v1 = v2.
  Proof.
    eapply INV1 in H1, H2. destruct H1 as [p1 H1], H2 as [p2 H2].
    pose proof (INV0 _ _ n _ _ H1 H2). easy.
  Qed.

  Lemma accept_after_chosen q n v a n' v'
    (QUORUM : Q q)
    (H1 : Chosen q (n, v))
    (H2 : n <= n')
    (H3 : Accepted a (n', v'))
    : v = v'.
  Proof.
    revert n v a v' H1 H2 H3.
    induction n' as [n' IH] using lt_wf_ind.
    intros. assert (n = n' \/ n < n') by lia. destruct H as [EQ|LT].
    - subst. destruct (quorum_nonempty _ QUORUM) as [a0 H].
      specialize (H1 _ H). eauto using accept_unique.
    - eapply INV1 in H3. destruct H3 as [p H]. eapply INV2 in H. destruct H as [q' [QUORUM' H]].
      destruct (NDISJ _ _ QUORUM QUORUM') as [a0 [HQ HQ']].
      destruct H. { exfalso. specialize (H1 _ HQ). firstorder. }
      unfold Occupied in H. destruct H as [n'' [DEC [[a1 [HQ1 H3']] H4]]].
      specialize (H4 a0 n v HQ' LT (H1 a0 HQ)).
      eapply (IH n''); eauto.
  Qed.

  Lemma safe_aux n1 v1 n2 v2
    (LE : n1 <= n2)
    (H1 : exists q, Q q /\ Chosen q (n1, v1))
    (H2 : exists q, Q q /\ Chosen q (n2, v2))
    : v1 = v2.
  Proof.
    destruct H1 as [q1 [HQ1 H1]], H2 as [q2 [HQ2 H2]].
    destruct (quorum_nonempty q2 HQ2) as [a H].
    specialize (H2 _ H). eapply (accept_after_chosen q1 n1 v1); eauto.
  Qed.

  Theorem safe n1 v1 n2 v2
    (H1 : exists q, Q q /\ Chosen q (n1, v1))
    (H2 : exists q, Q q /\ Chosen q (n2, v2))
    : v1 = v2.
  Proof.
    assert (n1 <= n2 \/ n2 <= n1) by lia. destruct H.
    - eapply safe_aux; eauto.
    - symmetry. eapply safe_aux; eauto.
  Qed.

End PAXOS.
