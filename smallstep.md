# 小步法

## Toy Language

### 基础定义

语句

```coq
Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)
```

函数计算

```coq
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.
```

关系计算

We use the notation t ==> n for "t evaluates to n."

```coq
Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

where " t '==>' n " := (eval t n).
```

单步推导

```coq
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2', (*这里规定了执行顺序*)
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').
```

### deterministic

```coq
Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
```

```coq
Theorem step_deterministic:
  deterministic step.
Proof.  
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PlusConstConst *) inversion Hy2; subst.
    + (* ST_PlusConstConst *) reflexivity.
    + (* ST_Plus1 *) inversion H2. (*这里C不可能再step了，也是没有constructor*)
    + (* ST_Plus2 *) inversion H2.
  - (* ST_Plus1 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
    + (* ST_Plus2 *)
      inversion Hy1.
  - (* ST_Plus2 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.
```

### Ltac

不断调用inversion和subst的Ltac

```coq
Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.
```

简化之前的证明：

```coq
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.
```

### Values

用于表示可终止程序的最终状态

```coq
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).
```

有了判定是否为值的命题后，可以重写step

```coq
-------------------------------(ST_PlusConstConst)
 P (C n1) (C n2) --> C (n1 + n2)


          t1 --> t1'
     --------------------     (ST_Plus1)
     P t1 t2 --> P t1' t2


           value v1
          t2 --> t2'
     --------------------     (ST_Plus2)
     P v1 t2 --> P v1 t2'
```

对应的coq语言

```coq
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').
```

在证明过程中，`value`可以被用来inversion得到`C`，进而discriminate

### Strong Progress and Normal Forms

一个程序要么是值要么存在下一个状态

```coq
Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
```

值不存下一步

没有下一步的是值（strong process 推论）

值等价于没有下一步的term

```coq
Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.
```

复习：contradiction策略自动推一系列矛盾

## Multi-Step Reduction

定义多步约简关系

```coq
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).
```


多步约简是自反的（包括0步约简）、包含所有的单步约简、是传递的

这是个传递闭包

```coq
Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
```

用eapply规避构造中间结果

### multi-step上的normal form

一个term要么能继续（多步）推导，要么是step的normal form（值）

```coq
Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

```


normalizing:如果一种规约最终一定有结果（noraml_form_of是一个全函数）

```coq
Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.
```