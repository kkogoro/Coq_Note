# 小步法


## 策略

### induction

对于Inductive Prop H，如果直接对H induction，会把H变成相应前提，比如

```coq
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
      (*step的类型对应这个最基础的情况*)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2', 
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').
```

中，如果对`t --> t'`归纳，那么会分别把`t --> t'` 跟 `P (C n1) (C n2) --> C (n1 + n2)` ，
`P t1 t2 --> P t1' t2` ， `P (C n1) t2 --> P (C n1) t2'` 匹配，并且对于constructor ST_Plus1, ST_Plus2，还会把前提`t1 --> t1'` 、
`t2 --> t2'` 填到H的位置。

对于被归纳的命题P，会自动从H中找到P的前提（前提可能已经提到前提区了）并应用上去得到当前归纳命题。比如

```coq
v1, t2, t2': tm
Hv: value v1
H: t2 -->* t2'
---
P v1 t2 -->* P v1 t2'
```

如果对H归纳，在`t2 --> y -> y -->* t2' -> t2 --> t2'` 这个分支上，会得到H和H0这两个前提

```coq
v1: tm
Hv: value v1
x, y, z: tm
H: x --> y
H0: y -->* z
IHmulti: P v1 y -->* P v1 z
---
P v1 x -->* P v1 z
```

注意IHmulti实际上是 `Hv -> H -> P v1 t2 -->* P v1 t2'` apply到H和H0上得到的归纳命题

### eexists

goal中有exists，可以eexists可以把它替换为存在变量

### normalize

Ltac，可以直接化简式子

```coq
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof. (*REVIEW*)
  eexists. split.
  - normalize.
  - constructor.
Qed.
```

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

`solve[A|B|C]`会依次尝试执行A B C策略，直到其中一个成功，如果都没成功就不执行。

详见`typechecking.md`

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
Definition relation (X : Type) := X -> X -> Prop.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(*证明关键：inversion (value v)得出v = C n*)

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

定义多步约简关系，传入一个X上的relation，返回一个X上的relation

```coq
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
(*multi_step会展开第一步step*)
Notation " t '-->*' t' " := (multi step t t') (at level 40).
```

注意step不是自反的，但是

多步约简是自反的（包括0步约简）、包含所有的单步约简、是传递的

这是个传递闭包

```coq
(*单步约简，把-->*转化为--> *)
Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.

(*传递性*)
Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
```

用eapply规避构造中间结果

### multi-step上的normal form

如果一个t可以经过0或多步约简到step normal form t'，我们就说t'是t的normal form

```coq
Definition step_normal_form := normal_form step.
(*定义t'为t的normal form*)
Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

```

#### determinisic multi-step

```coq
Theorem normal_forms_unique:
  deterministic normal_form_of.

(*证明思路是induction第一个derivation再inversion第二个*)
```

#### normalizing

normalizing: 一种relation的性质，如果一种规约（relation）最终一定有normal form的结果（noraml_form_of是一个全函数）。也即一个term要么能继续（一步或多步）推导到normal form，要么就是（0步）step的normal form（值）

```coq
Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.
```

下证step是normalizing的

先证两个引理

```coq
Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.

Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.

(*这俩证明思路就是induction*)
```

```coq
Theorem step_normalizing : (*REVIEW*)
  normalizing step
```

## 大步法与小步法等价性

### 大步法推小步法

```coq
Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.
```

这里大步法只关心结果，因为都相当于是Aexp

### 小步法推大步法

一个引理

```coq
Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
```

```coq
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
(* 证明思路：
  先assert(exists n, t'= C n)，用nf与value的等价性证明

  然后induction(t-->*t')
  用引理完成multi_step部分的证明
   *)
```

## 小步法IMP

把skip作为com的normal form，赋值语句规约成skip，seq在第一句被规约为skip后就直接删去第一句，然后开始对右面的代码规约

把while 规约为if + while

注意其中的所有nat都是包裹在`<{}>`中的，会被自动解析成 Anum(nat)，不存在类型问题，当然true false也同理会被解析成BTrue BFalse

### aexp

```coq
(*判定aexp是否被规约为normal*)
Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).
(*aexp规约步骤*)
Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').
```

### bexp

```coq
Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
(*注意and如何解析*)
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').
```

### com

执行com会修改st，所以规约式前后都要有st

```coq
Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  (*IF的策略是按照bool选好选择支*)
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  (*While的策略是每次展开一层*)
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).
```

## 并行IMP

```coq
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW: c1||c2 *)

Notation "x || y" :=
         (CPar x y)
           (in custom com at level 90, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
(*新增*)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

(*同时定义多步*)
Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).
```

相关证明： 每次先eapply multi_step，然后apply CS_Par1/2选定并行分支，然后对应到哪个部分先apply CS_Step把内部每个结构化为最简（要用BS、AS，用state查值可能要simpl. rewrite. apply t_update_eq.）
