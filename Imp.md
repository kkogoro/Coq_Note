# Imp

## 语义

### nat

建模成函数

```coq
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.
```

nat上的优化

```coq
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.
```

### bool

建模成函数

```coq
Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.
```

bool上的优化

```coq
Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with 
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BNeq a1 a2 => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
end.
```

### 建模成关系

#### Inference Rule Notation

```coq
| E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (APlus e1 e2) (n1 + n2)

| E_APlus (e1 e2 : aexp) (n1 n2 : nat)
    (H1 : aevalR e1 n1)
    (H2 : aevalR e2 n2) :
    aevalR (APlus e1 e2) (n1 + n2)

| E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) ->
    (e2 ==> n2) ->
    (APlus e1 e2)  ==> (n1 + n2)
```

等价于

```coq
       e1 ==> n1
       e2 ==> n2
 --------------------                (E_APlus)
 APlus e1 e2 ==> n1+n2
```

#### aevalR

```coq
Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.
```

#### bevalR

```coq
Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : BTrue ==>b true
  | E_BFalse : BFalse ==>b false
  | E_BEq (a1 a2: aexp): (BEq a1 a2) ==>b ((aeval a1) =? (aeval a2)) 
  | E_BNeq (a1 a2: aexp): (BNeq a1 a2) ==>b (negb ((aeval a1) =? (aeval a2)))
  | E_BLe (a1 a2: aexp):  (BLe a1 a2) ==>b (aeval a1) <=? (aeval a2)
  | E_BGt (a1 a2: aexp): (BGt a1 a2)  ==>b (negb ((aeval a1) <=? (aeval a2)))
  | E_BNot (e1: bexp) (b1: bool): (e1 ==>b b1) -> (BNot e1) ==>b (negb b1)
  | E_BAnd (e1 e2: bexp) (b1 b2: bool) : (e1 ==>b b1) -> (e2 ==>b b2) -> (BAnd e1 e2) ==>b (andb b1 b2)

where "e '==>b' b" := (bevalR e b) : type_scope.
```

### 函数与关系的等价性

#### 两种方法的区别

建模成函数更容易让coq自行计算，但是必须为total function，也即对每种输入都要给出输出；

建模成关系不需要对每种关系都给出输出，例如while true没有输出，只需要是partial function，同时对于aeval我们可以定义NaN来表示除以0

One point in favor of relational definitions is that they can bemore elegant and easier to understand.

Another is that Coq automatically generates nice inversion and induction principles from [Inductive] definitions.

On the other hand, functional definitions can often be more convenient: Functions are automatically deterministic and total; but for a relational definition, we have to _prove_ these properties explicitly if we need them.

With functions we can also take advantage of Coq's computation mechanism to simplify expressions during proofs.

#### aeval

```coq
Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.
```

#### beval

```coq
Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  split.
  - intros H. (*H是命题，但是可以返回多种命题，需要分类讨论*)
    induction H;
    subst; reflexivity.
  - generalize dependent bv.
    induction b;
    intros; subst; simpl; constructor.
    + apply IHb. reflexivity.
    + apply IHb1. reflexivity.
    + apply IHb2. reflexivity.
Qed.
```

#### 加入变量支持

```coq
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
```

修改eval支持变量(注意这里用notation优化了写法，和前面对应一下)

```coq
Fixpoint aeval (st : state) (* <--- NEW *)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *)
               (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

(** We can use our notation for total maps in the specific case of
    states -- i.e., we write the empty state as [(_ !-> 0)]. *)

Definition empty_st := (_ !-> 0).

(** Also, we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).
```

## Commands

```coq
Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** As we did for expressions, we can use a few [Notation]
    declarations to make reading and writing Imp programs more
    convenient. *)

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.
```

注意是`;`右结合的，所以apply E_Seq只能从第一条指令解析

### 关闭语法糖

```coq
[Unset Printing Notations] (undo with [Set Printing Notations])
[Set Printing Coercions] (undo with [Unset Printing Coercions])

[Set Printing All] (undo with [Unset Printing All])
```

## Evaluating Commands

### Evaluation as a Function

不能对循环语句定义eval，因为可能有潜在的无限循环，无法停机，coq不允许无法停机的函数

```coq
(*
    Here is an example showing what would go wrong if Coq allowed
    non-terminating recursive functions:*)

Fixpoint loop_false (n : nat) : False := loop_false n.
(*
    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which would be
    a disaster for Coq's logical consistency.*)
```

### Evaluation as a Relation

#### Operational Semantics

```coq
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').
```

#### E_Seq

`apply E_Seq with (st' := (X !-> 2)).` 等价于 `apply E_Seq with (X !-> 2).`

一方面我们可以用 `apply  E_Seq` 来查看缺少的是哪个变量。另一方面，apply一定匹配的是右侧的Prop，对应到当前goal，缺的就是`st'`

#### E_Asgn

注意是把新的值附在map最前面，对应E_Seq时要把后赋值的变量放在状态前面

### Determinism of Evaluation

证明同一个状态经过同样语句后状态相同

```coq
Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
  inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.
```

### Reasoning About Imp Programs

```coq
Lemma t_update_eq : forall (A : Type) (m : total_map A) (x : string) (v : A),
       (x !-> v; m) x = v
```


```coq
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
      contradictory and so can be solved in one step with
      [discriminate]. *)

  induction contra; subst; (*这里是按照ceval构造的*)
  (*因为使用了induction，如果没有递归构造子前提会默认丢失contra*)
  try discriminate.
  - (*E_WhileFalse*)
    inversion Heqloopdef. (*代替injection*)
    rewrite H1 in H. discriminate. 
  - (*E_WhileTrue*)
    apply IHcontra2. apply Heqloopdef.
Qed.   
```

```coq
Theorem no_whiles_terminating: 
  forall c, no_whilesR c -> forall st, exists st', st =[ c ]=> st'.
  (*如果把st写到第一个forall需要一开始generlize dependent*)
Proof.
  intros c H.
  induction H; subst; intros st.
  - exists st.
    constructor.
  - exists (X0 !-> aeval st a; st).
    constructor.
    reflexivity.
  - 
    destruct (IHno_whilesR1 st) as [st' IH1].
    destruct (IHno_whilesR2 st') as [st'' IH2].
    exists st''.
    apply E_Seq with st';
    assumption.
  - destruct IHno_whilesR1 with (st:=st) as [st' IH1].
    destruct IHno_whilesR2 with (st:=st) as [st'' IH2].
    destruct (beval st b) eqn:E. (*注意这里destruct (beval st b)*)
    + exists st'.
      apply E_IfTrue; assumption.
    + exists st''.
      apply E_IfFalse; assumption.
Qed.
```

## 策略

### reapeat

keeps applying this tactic until it fails or until it succeeds but doesn't make any progress

常和`try` `;`一起用

如果是一直会成功的则会死循环，比如reapeat add_comm

### subst

`subst x` 将所有含`x=...`的等式中的`x`换为`...`

```coq

```

### constructor

寻找一个可以匹配目标的归纳定义构造函数`c`，并执行`apply c`. 不可以提供额外参数（？）

```coq
(*goal*)
BAnd b1 b2 ==>b beval b1 && beval b2
---
apply E_BAnd.

---

(*new goal*)
(1/2)
b1 ==>b beval b1
(2/2)
b2 ==>b beval b2
```

上面的做法等价于直接执行`constructor.`，coq会自动帮你寻找合适的constructors

### induction more

对`E1: st =[ c ]=> st1` 其中 `c` 未知时，可以直接 `induction E1` 将`c`分类归纳

### inversion

#### 分解前提

`inversion H`将会分类讨论前提`H`是由什么构造函数、什么元素构造出来的，并自动匹配，分为多个子前提，可能会引入新的变量。

例如对`H: st =[ skip; c ]=> st'` inversion将会得到

```coq
H: st =[ skip; c ]=> st'
c1, c2: com
st0, st'0, st'': state
H2: st =[ skip ]=> st'0
H5: st'0 =[ c ]=> st'
H0: c1 = <{ skip }>
H1: c2 = c
H3: st0 = st
H4: st'' = st'
```

这是因为:首先有语法糖`where "st =[ c ]=> st'" := (ceval c st st').`，而后Coq将自动匹配发现`H`是由`E_Seq`构造函数构造出来的，其中`E_Seq : forall c1 c2 st st' st'',st  =[ c1 ]=> st' -> st' =[ c2 ]=> st'' -> st  =[ c1 ; c2 ]=> st''`

相应的，对`<{ if b then c1 else c2 end }>`的分解则会分成True和False两种情况(两种前提，分别证明)，若给出b则有一个可以discriminate

#### 分类讨论

执行destruct和injection的功能，但是会做更多工作，更利于证明。通常后面接`subst`

#### discriminate

替代discriminate

#### lia

如果goal是由数字常量、数字运算符(S\pred)、乘以常数、等于和不等关系、大小关系、逻辑连词构成，则可以通过lia解决正确的goal，若失败，则goal是false

#### contradiction

找到等价于False的命题并discriminate

## 证明方法

当`st =[c1;c2]=> st'`出现在前提时，使用`inversion`匹配constructor将他们分解为两个前提

当`st =[c1;c2]=> st'`出现在目标时，使用`apply E_Seq`来分解为两个子目标

当需要对目标中`If b then c1 else c2 end`讨论分支时，`destruct (beval st b)`是更好的选择