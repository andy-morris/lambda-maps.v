Require Import Program.

Create HintDb map discriminated.

Delimit Scope map_scope with m.
Local Open Scope map_scope.

Inductive map1 :=
| One
| Inl (m: map1)
| Inr (n: map1)
| Cons (m n: map1).

Inductive map :=
| Zero
| M (m: map1).


Bind Scope map_scope with map1 map.

Notation "0" := Zero: map_scope.
Notation "[ m ]" := (M m): map_scope.
Notation "1" := One: map_scope.


Function mapp (m n: map): map :=
  match m, n with
  | 0,   0   => 0
  | [m], 0   => [Inl m]
  | 0,   [n] => [Inr n]
  | [m], [n] => [Cons m n]
  end.
Infix "&" := mapp (at level 40, no associativity): map_scope.

Ltac split_0 := change 0 with (0 & 0).

Theorem mapp_0 m n: m & n = 0 -> m = 0 /\ n = 0.
Proof. now destruct m, n. Qed.

Corollary mapp_0_l m n: m & n = 0 -> m = 0.
Proof. apply mapp_0. Qed.

Corollary mapp_0_r m n: m & n = 0 -> n = 0.
Proof. apply mapp_0. Qed.

Hint Resolve mapp_0 mapp_0_l mapp_0_r: map.

Theorem mapp_inj m1 m2 n1 n2:
  m1 & n1 = m2 & n2 ->
  m1 = m2 /\ n1 = n2.
Proof.
  destruct m1, n1, m2, n2; simpl; intuition congruence.
Qed.

Theorem mapp_1 m n: m & n <> [1].
Proof. functional inversion 1. Qed.

Ltac mapp_1 :=
  match goal with
  | H: ?m & ?n = [1] |- _ =>
      contradict H; apply mapp_1
  end.
Hint Extern 1 => mapp_1: map.

Program Fixpoint unmapp m: option (map * map) :=
  match m with
  | [1]        => None
  | 0          => Some (0,   0)
  | [Inl m]    => Some ([m], 0)
  | [Inr n]    => Some (0,   [n])
  | [Cons m n] => Some ([m], [n])
  end.

Theorem unmapp_none m: unmapp m = None -> m = [1].
Proof. now destruct m as [| []]. Qed.

Theorem mapp_unmapp m n: unmapp (m & n) = Some (m, n).
Proof. now destruct m as [| []], n as [| []]. Qed.


Reserved Infix "⊥" (at level 50, no associativity).
Inductive orth: map -> map -> Prop :=
| OZeroL n: 0 ⊥ n
| OZeroR m: m ⊥ 0
| OMApp  m1 m2 n1 n2:
    m1 ⊥ m2 ->
    n1 ⊥ n2 ->
    m1 & n1 ⊥ m2 & n2
where "m ⊥ n" := (orth m n): map_scope.
Hint Constructors orth: map.

Theorem orth_symm m n: m ⊥ n -> n ⊥ m.
Proof. induction 1; auto with map. Qed.
Hint Immediate orth_symm: map.

Theorem orth_1 m: [1] ⊥ m -> m = 0.
Proof. inversion 1; auto with map. Qed.
Hint Resolve orth_1: map.