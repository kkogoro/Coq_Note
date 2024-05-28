# map

## def

```coq
Definition total_map (A : Type) := string -> A.
Definition partial_map (A : Type) := total_map (option A).
```

partial_map就是把string映射到Some A

## Locate

用于确定都在哪里定义了notation

```coq
Locate "+".
---
Notation "{ A } + { B }" := (sumbool A B) : type_scope
  (default interpretation)
Notation "A + { B }" := (sumor A B) : type_scope (default interpretation)
Notation "x + y" := (Init.Nat.add x y) : nat_scope (default interpretation)
Notation "x + y" := (sum x y) : type_scope
```

进一步，想查看Init.Nat.add是怎么定义的

```coq
Print Init.Nat.add.
---
Init.Nat.add =
fix add (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end
	 : nat -> nat -> nat

Arguments Init.Nat.add (n m)%nat_scope
```



## Total map

```coq
Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.
Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.
Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).

```

```coq
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  intros.
  unfold t_empty.
  reflexivity.
Qed.
```

### eqb_spec

直接讨论x1 x的关系，替换所有`=?string`和`=`

```coq

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  apply functional_extensionality.
  unfold t_update.
  intros. (*eqb_spec x1 x要和后面x1=?x顺序相同*)
  destruct (eqb_spec x1 x) as [H1 | H1];
  destruct (eqb_spec x2 x) as [H2 | H2];
  try reflexivity.
  exfalso.
  apply H.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.
```

```coq
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
```

## partial map

```coq
Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
```

## 其他

有时候`simpl.`不会展开map的计算，需要手动`unfold t_update`和`unfold t_empty` （比如在eapply中）

可能是因为存在变量的type未知，可以在任意时刻`refl`给存在变量赋值，所以`simpl`趋向于保守策略