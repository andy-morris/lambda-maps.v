Require Import Map.
Local Open Scope map_scope.

Require PeanoNat.
Require Import Program.

Create HintDb term discriminated.

Delimit Scope term_scope with t.
Local Open Scope term_scope.

Reserved Notation "[ ]".
Reserved Notation "[ x ]".
Reserved Infix "@" (at level 20, left associativity).
Reserved Infix "\" (at level 30, right associativity).
Reserved Infix "//" (at level 50, no associativity).
Reserved Notation "x ## s" (at level 50, no associativity).
Reserved Infix "\\" (at level 30, no associativity).


Local Ltac decide_right Q :=
  pattern Q; apply decide_right; [easy | intros _].

Local Ltac decide_left Q :=
  pattern Q; apply decide_left; [easy | intros _].


Module Id := PeanoNat.Nat.

Definition id := Id.t.

Definition id_eq := Id.eq_dec.


Inductive term :=
| Box
| Free (y: id)
| App (s t: term)
| Abs (n: map) (s: term).

Bind Scope term_scope with term.

Notation "[ ]" := Box (format "[ ]"): term_scope.
Notation "[ x ]" := (Free x): term_scope.
Infix "@" := App: term_scope.
Infix "\" := Abs: term_scope.


Function occb x s :=
  match s with
  | []    => false
  | [y]   => if id_eq x y then true else false
  | s @ t => occb x s || occb x t
  | _ \ s => occb x s
  end%bool.

Notation "x ## s" := (occb x s = false): term_scope.

Theorem occb_app x s1 s2:
  x ## (s1 @ s2) <-> x ## s1 /\ x ## s2.
Proof.
  split.
  - now intros []%Bool.orb_false_elim.
  - intros []; apply Bool.orb_false_intro; easy.
Qed.


Inductive dvd: map -> term -> Prop :=
| DBox0:    0   // []
| DBox1:    [1] // []
| DFree y:  0   // [y]
| DApp m s n t:
    m // s ->
    n // t ->
    m & n // s @ t
| DAbs m n s:
    m ⊥ n ->
    m // s ->
    n // s ->
    m // n \ s
where "m // s" := (dvd m s): term_scope.
Hint Constructors dvd: term.

Notation map_for s := {m | m // s}.

Notation wf := (dvd 0).
Notation wfterm := {t | wf t}.

Lemma div_wf n s: n // s -> wf s.
Proof. induction 1; split_0; auto with map term. Qed.

Lemma div_app m s n t:
  (m & n) // (s @ t) ->
  m // s /\ n // t.
Proof. inversion 1; mapp_inj; subst; auto. Qed.

Lemma div_abs m n s: m // n \ s -> m // s.
Proof. now inversion 1. Qed.

Corollary wf_app s t: wf (s @ t) <-> wf s /\ wf t.
Proof. split_0; split; [apply div_app | intros []; auto with term]. Qed.

Ltac div_app :=
  match goal with
  | H: (_ & _) // (_ @ _) |- _ =>
      let H1 := fresh H in
      let H2 := fresh H in
      apply div_app in H as [H1 H2]
  | H: wf (_ @ _) |- _ =>
      let H1 := fresh H in
      let H2 := fresh H in
      apply wf_app in H as [H1 H2]
  end.
Hint Extern 3 => div_app: term.

(* uses PI *)
Theorem wf_eq (s t: wfterm): `s = `t -> s = t.
Proof. destruct s, t; apply subset_eq_compat. Qed.

Hint Resolve div_wf div_abs wf_eq: term.


Function fill (s: term) (m: map) (e: term): option term :=
  match s with
  | [] =>
      match m with
      | 0   => Some []
      | M 1 => Some e
      | _   => None
      end
  | [y] =>
      match m with
      | 0 => Some [y]
      | _ => None
      end
  | s1 @ s2 =>
      match unmapp m with
      | Some (m1, m2) =>
          match fill s1 m1 e, fill s2 m2 e with
          | Some t1, Some t2 => Some (t1 @ t2)
          | _,       _       => None
          end
      | None => None
      end
  | n \ s' =>
      match fill s' m e with
      | Some t => Some (n \ t)
      | None   => None
      end
  end.

Theorem fill_some s m e:
  wf s -> m // s -> exists r, fill s m e = Some r.
Proof.
  intro S; induction 1; simpl; eauto.
  - destruct IHdvd1 as [? R1], IHdvd2 as [? R2]; eauto with term.
    rewrite mapp_unmapp, R1, R2; eauto.
  - destruct IHdvd1 as [? R]; eauto with term.
    rewrite R; eauto.
Qed.

Theorem fill_0 s e r:
  fill s 0 e = Some r -> r = s.
Proof.
  revert r.
  remember 0 as m.
  functional induction (fill s m e); try congruence; intros r R.
  - inversion e1; inversion R; subst; f_equal; auto.
  - inversion R; subst; f_equal; auto.
Qed.

Theorem fill_div s m e r n:
  n // s -> m // s -> m ⊥ n ->
  wf s -> wf e -> fill s m e = Some r ->
  n // r.
Proof.
  intro NS; revert m r.
  induction NS as [| | | p1 ? p2 | p]; intros m r MS MN S E R;
    try solve [functional inversion R; now subst].
  - functional inversion R; subst.
    + eauto with term.
    + now apply orth_1 in MN.
  - functional inversion R; subst.
    replace m with (m1 & m2) in *; [orth_inj |].
    + constructor; eauto with term.
    + pose proof (mapp_unmapp m1 m2).
      apply unmapp_inj; congruence.
  - apply div_abs in S.
    inversion MS; subst.
    functional inversion R; subst.
    constructor; eauto.
Qed.

Theorem fill_wf s m e r:
  wf s -> m // s -> wf e -> fill s m e = Some r -> wf r.
Proof.
  revert r.
  functional induction (fill s m e);
    intros r S MS E R; inversion R; subst; auto.
  - rewrite (mapp_unmapp' m m1 m2) in MS; auto.
    apply wf_app; split.
    + apply IHo; eauto with term.
    + apply IHo0; eauto with term.
  - inversion MS; subst.
    apply div_abs in S.
    constructor; auto with map.
    apply fill_div with (s := s') (m := m) (e := e); auto.
Qed.


Fixpoint make_map x s :=
  match s with
  | []    => 0
  | [y]   => if id_eq x y then M 1 else 0
  | s @ t => make_map x s & make_map x t
  | _ \ s => make_map x s
  end.

Fixpoint make_skel x s :=
  match s with
  | []    => []
  | [y]   => if id_eq x y then [] else [y]
  | s @ t => make_skel x s @ make_skel x t
  | n \ s => n \ make_skel x s
  end.

Theorem make_map_orth x s m:
  m // s -> make_map x s ⊥ m.
Proof.
  revert m; induction s; simpl;
    inversion_clear 1; auto with map term.
Qed.
Hint Resolve make_map_orth: term.

Lemma make_skel_div x s m:
  wf s -> m // s -> m // make_skel x s.
Proof with (auto with term).
  revert m. induction s; intros m S MS; simpl; auto.
  - destruct (id_eq x y); inversion MS; subst...
  - inversion_clear MS...
  - inversion_clear MS; apply div_abs in S...
Qed.
Hint Resolve make_skel_div: term.

Theorem make_map_skel_div x s:
  wf s -> make_map x s // make_skel x s.
Proof with (simpl; eauto with term).
  induction s; intro S...
  - destruct (id_eq x y)...
  - inversion_clear S; constructor...
Qed.
Hint Resolve make_map_skel_div: term.

Theorem make_skel_wf x s: wf s -> wf (make_skel x s).
Proof with (auto with term).
  induction s; intro S; simpl...
  - destruct (id_eq x y)...
  - split_0; constructor...
  - inversion_clear S...
Qed.
Hint Resolve make_skel_wf: term.

Theorem make_map_not_occ x s: x ## s -> make_map x s = 0.
Proof.
  intro S.
  induction s; auto.
  - functional inversion S; subst; simpl.
    now rewrite H1.
  - apply occb_app in S as [].
    simpl; split_0; f_equal; auto.
Qed.
Hint Resolve make_map_not_occ: term.

Theorem make_skel_not_occ x s: x ## make_skel x s.
Proof.
  induction s; auto.
  - simpl.
    destruct (id_eq x y); simpl; auto.
    decide_right (id_eq x y); auto.
  - now apply occb_app.
Qed.
Hint Resolve make_skel_not_occ: term.

Theorem make_skel_occ_diff x s z:
  x <> z ->
  occb z s = occb z (make_skel x s).
Proof.
  intro XY; induction s; auto.
  - simpl. destruct (id_eq z y), (id_eq x y); subst; simpl.
    + congruence.
    + now decide_left (id_eq y y).
    + easy.
    + now decide_right (id_eq z y).
  - simpl; f_equal; easy.
Qed.

Theorem make_skel_not_occ_eq x s:
  x ## s -> make_skel x s = s.
Proof.
  intro X.
  induction s; auto.
  - simpl. functional inversion X; subst.
    now decide_right (id_eq x y).
  - apply occb_app in X as [].
    simpl; f_equal; auto.
  - simpl in *; f_equal; auto.
Qed.
Hint Resolve make_skel_not_occ_eq: term.

Definition subst s x :=
  fill (make_skel x s) (make_map x s).

Theorem subst_wf s x e r:
  wf s -> wf e -> subst s x e = Some r -> wf r.
Proof.
  unfold subst. intros.
  apply fill_wf with (s := make_skel x s) (m := make_map x s) (e := e);
    auto with term.
Qed.

Section Subst_subterms.
  Local Arguments subst s x /.

  Theorem subst_self x s: subst s x [x] = Some s.
  Proof.
    induction s; simpl in *; auto.
    - destruct (id_eq x y); simpl; congruence.
    - now rewrite mapp_unmapp, IHs1, IHs2.
    - now rewrite IHs.
  Qed.

  Lemma subst_box x e: subst [] x e = Some [].
  Proof. easy. Qed.

  Lemma subst_free_eq x e: subst [x] x e = Some e.
  Proof. simpl; destruct (id_eq x x); easy. Qed.

  Lemma subst_free_ne x y e:
    x <> y -> subst [y] x e = Some [y].
  Proof. intro; simpl; destruct (id_eq x y); easy. Qed.

  Lemma subst_app s1 s2 x e r1 r2:
    subst s1 x e = Some r1 ->
    subst s2 x e = Some r2 ->
    subst (s1 @ s2) x e = Some (r1 @ r2).
  Proof. simpl; rewrite mapp_unmapp; intros -> ->; easy. Qed.

  Lemma subst_abs n s x e r:
    subst s x e = Some r ->
    subst (n \ s) x e = Some (n \ r).
  Proof. simpl; intros ->; easy. Qed.

  Lemma subst_app_split s1 s2 x e r:
    subst (s1 @ s2) x e = Some r ->
    exists r1 r2,
      r = r1 @ r2 /\
      subst s1 x e = Some r1 /\
      subst s2 x e = Some r2.
  Proof.
    simpl.
    rewrite mapp_unmapp.
    destruct fill, fill; try easy.
    inversion 1; eauto.
  Qed.

  Lemma subst_abs_split n s x e r:
    subst (n \ s) x e = Some r ->
    exists r',
      r = n \ r' /\
      subst s x e = Some r'.
  Proof.
    simpl.
    destruct fill; try easy.
    inversion 1; eauto.
  Qed.
End Subst_subterms.

Hint Rewrite
  subst_box subst_free_eq subst_free_ne subst_app subst_abs
  using solve [auto]: subst.


Lemma subst_not_occ s x e:
  x ## s -> subst s x e = Some s.
Proof.
  induction s; simpl; intro XS; auto.
  - unfold subst; simpl.
    now destruct (id_eq x y).
  - apply occb_app in XS as [].
    erewrite subst_app; eauto.
  - unfold subst; simpl. fold (subst s x).
    rewrite IHs; auto.
Qed.

Ltac invert_some :=
  match goal with
  | H: Some _ = Some _ |- _ =>
      inversion H; subst; clear H; simpl in *
  end.

Ltac subst_app_split :=
  (* these two matches can't be merged :/ *)
  match goal with
  | a: term |- _ =>
    match goal with
      | H: subst (_ @ _) _ _ = Some a |- _ =>
          let a1 := fresh a in let a2 := fresh a in
          let H1 := fresh H in let H2 := fresh H in
          apply subst_app_split in H as (a1 & a2 & -> & H1 & H2)
    end
  end.

Ltac subst_abs_split :=
  match goal with
  | a: term |- _ =>
      match goal with
      | H: subst (_ \ _) _ _ = Some a |- _ =>
          let a' := fresh a in let H' := fresh H in
          apply subst_abs_split in H as (a' & -> & H')
      end
  end.

Ltac simpl_subst := progress repeat
  (invert_some + subst_app_split + subst_abs_split +
   (progress autorewrite with subst in *)).


Theorem substitution:
  forall a x1 e1 x2 e2 a1 a2 e1' r1 r2,
  x1 <> x2 ->
  x1 ## e2 ->
  subst a  x1 e1  = Some a1  ->
  subst a1 x2 e2  = Some r1  ->
  subst a  x2 e2  = Some a2  ->
  subst e1 x2 e2  = Some e1' ->
  subst a2 x1 e1' = Some r2  ->
  r1 = r2.
Proof.
  intros until r2; intros X XE A1 R1 A2 E1' R2.
  revert a1 a2 r1 r2 A1 A2 R1 R2.
  induction a; intros.
  - now simpl_subst.
  - destruct (id_eq x1 y), (id_eq x2 y); subst.
    + contradiction.
    + simpl_subst; congruence.
    + simpl_subst; rewrite subst_not_occ in R2; congruence.
    + now simpl_subst.
  - simpl_subst; f_equal; eauto.
  - simpl_subst; f_equal; eauto.
Qed.


Definition lam x s :=
  make_map x s \ make_skel x s.
Infix "\\" := lam: term.


Theorem subst_lam_eq x s e:
  subst (lam x s) x e = Some (lam x s).
Proof. apply subst_not_occ, make_skel_not_occ. Qed.

Theorem subst_lam_not_occ x s y e:
  y ## s ->
  subst (lam x s) y e = Some (lam x s).
Proof.
  intro; destruct (id_eq x y) as [-> | ].
  + apply subst_lam_eq.
  + apply subst_not_occ; simpl.
    rewrite <- make_skel_occ_diff; auto.
Qed.
