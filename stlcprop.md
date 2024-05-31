# STLCProp

来证明一些STLC的命题

## Canonical Forms

仿照types一章，我们需要给出每种类型正确（well-typed）的closed term的Canonical Forms（为value时的形态）.

而closed term要求我们的term没有任何自由变量就能推导出类型，也就是说我们没有任何关于term中变量类型的先验知识，也就是context Gamma为空。

具体来说，Bool的value一定是True或False，Arrow type的value一定是一个abs。app不可能是value，更不可能是Canonical Forms。

```coq
Lemma canonical_forms_bool : forall t,
  empty |-- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT. (*abs必然是arrow type，与bool矛盾*)
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (T1 -> T2) ->
  value t -> (*这是很强的限制*)
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |]; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.
```

定义好这两个Canonical Forms我们就可以更方便地证明进展性和保持类型性了。

## 进展性Progress

```coq
empty x0 = Some T1
(*等价于*)
 (_ !-> None) x0 = Some T1
```

```coq
apply_empty: forall (A : Type) (x : string), 
            empty x = None
```

证明Progress，用纸笔写一写就很清楚了

```coq

Theorem progress' : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto; (*直接解决abs true false的情况*)
  inversion Ht; subst; clear Ht.
  - (*var*)
    rewrite apply_empty in H1.
    discriminate.
  - (*app*)
    right.
    destruct (IHt1 <{T2 -> T}> H2) as [Ht1 | Ht1].
    + (*value t1*)
      destruct (IHt2 T2 H4) as [Ht2 | Ht2].
      * (*value t2*)
        apply canonical_forms_fun in H2; [| assumption]. (*这里是为了消除显然的第二个分支*)
        destruct H2 as [x [u H2]].
        subst.
        exists <{[x := t2] u}>.
        apply ST_AppAbs.
        assumption.
      * (* t2 -> t2' *)
        destruct Ht2 as [t2' Ht2].
        exists <{ t1 t2' }>.
        apply ST_App2; assumption.
    + (*t1 -> t1'*)
      destruct Ht1 as [t1' Ht1].
      exists <{ t1' t2 }>.
      apply ST_App1.
      assumption.
  - (*If*)
    right.
    destruct (IHt1 <{Bool}> H3) as [Ht1 | Ht1].
    + (*value t1*)
      apply canonical_forms_bool in H3; [| assumption].
      destruct H3 as [H3 | H3]; rewrite H3.
      * eexists. apply ST_IfTrue.
      * eexists. apply ST_IfFalse.
    + (* t1 -> t1'*)  
      destruct Ht1 as [t1' Ht1].
      eexists. apply ST_If. apply Ht1.
Qed.
```

## 保类型Preservation

### weakening lemma

首先在map中定义过map的包含关系以及同时update不改变包含关系：

下面命题表示m含于m'

```coq
Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
```


引理：我们可以把context扩大

```coq
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
```

立刻得到推论，空的context可以替换为任意context

```coq
Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
  (*这里disc的是empty x = Some v*)
Qed. 
```

### The Substitution Lemma

替换引理：已知term t中有自由变量x，若我们给出x的类型为U的先验知识就能推出t的类型是T，那么对于任意无自由变量且类型为U的term v，我们将t中的每个x替换为v，仍然能推出t的类型是T

注意这里需要在空的上下文推出v的类型，因为v是value

```coq
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
```

当然更好的解读是

```coq
forall (Gamma : partial_map ty) (x0 : string) (U : ty) (t : tm) (T : ty), 
    (x0 |-> U; Gamma |-- t \in T) ->
forall v : tm, (empty |-- v \in U) -> Gamma |-- [x0 := v] t \in T
```

有了这个引理，我们就可以把substi中的类型推断分为两个阶段：v的类型推断和t的类型推断。我们可以分别推断t和v的类型，然后直接推出替换后的类型。

### 主定理证明

```coq
Theorem preservation : forall t t' T,
  empty |-- t \in T  ->
  t --> t'  ->
  empty |-- t' \in T.
```

## soundnesss

利用progess和preservation可以证明类型正确的stlc不会卡住

```coq
Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary type_soundness : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
```


## 唯一性

给定上下文的term类型唯一

这里选择对typing归纳，因为可以同时得到term的结构和type结构，只对term归纳还要对两个typing分别inversion才能获得type结构

```coq
Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof.
  intros Gamma e T T' HT HT'.
  generalize dependent T'.
  induction HT; subst; intros T' HT';
  inversion HT'; subst; clear HT'.
  - rewrite H in H2.
    injection H2 as H2.
    assumption.
  - rename t1 into t2.
    apply IHHT in H4.
    rewrite H4.
    reflexivity.
  - (*t2没用*)
    apply IHHT1 in H2.
    injection H2 as H2 H3.
    assumption.
  - reflexivity.
  - reflexivity.
  - apply IHHT2.
    assumption.
Qed.
```