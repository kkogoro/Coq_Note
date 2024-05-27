# Type Systems

类型系统只能用于证明没有某类错误：跨类型错误赋值

不能证明有某类错误：通不过类型检查不代表运行结果不对

## Typed Arithmetic Expressions

### 语法

```coq
t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
```

### 类型

一个bool与nat混用的类型

```coq
Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.
```

### 操作语义

注意pred和succ的约简顺序，最后会保留的只有0、succ、true、false，没有pred，含有pred的式子必然不是value（value的定义中也没有pred），还能约简

```coq
(** Here is the single-step relation, first informally...

       -------------------------------            (ST_IfTrue)
       if true then t1 else t2 --> t1

       -------------------------------       (ST_IfFalse)
       if false then t1 else t2 --> t2

                   t1 --> t1'
------------------------------------------------      (ST_If)
if t1 then t2 else t3 --> if t1' then t2 else t3

                 t1 --> t1'
             --------------------                 (ST_Succ)
             succ t1 --> succ t1'

               ------------                  (ST_Pred0)
               pred 0 --> 0

             numeric value v
            -------------------            (ST_PredSucc)
            pred (succ v) --> v

                  t1 --> t1'
             --------------------           (ST_Pred)
             pred t1 --> pred t1'

              -----------------            (ST_IsZero0)
              iszero 0 --> true

             numeric value v
          -------------------------         (ST_IszeroSucc)
          iszero (succ v) --> false

                t1 --> t1'
           ------------------------             (ST_Iszero)
           iszero t1 --> iszero t1'
*)
```

由于是小步法语义，` succ (if true then true else true)`是可以继续step的，但是内部最终归约到`true`时，`succ true`就不能继续step了

给出coq定义

```coq
Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.
```

### Normal Forms and Values

strong progress theorem：失效 （一个程序要么是值要么存在下一个状态）

normal forms: 不能继续规约的程序

但是此处的语言存在非值的normal form: 如succ true，称为卡住的项stuck

```coq
Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

(*normal_form =
fun (X : Type) (R : relation X) (t : X) => ~ (exists t' : X, R t t') *)
```

但是value仍然是normal form的子集，所以我没有错误的定义出能继续规约的value

```coq
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t H. 
  destruct H as [H | H].
  - inversion H; subst;
    intros contra;
    destruct contra;
    inversion H0.
  - induction H. (*Induction*)
    + intros contra.
      destruct contra.
      inversion H.
    + intros contra.
      destruct contra.
      inversion H0; subst; clear H0.
      unfold step_normal_form in IHnvalue.
       (*REIVEW*)
      apply IHnvalue.
      exists t1'.
      assumption.
Qed.
(*关键在于nvalue部分的证明，由于nvalue是递归定义的，所以要先在纸上分析好策略，因为对于goal: Succ t -/-> t'我们要用step中的ST_Succ来inversion并推翻，就需要证明t-->t'是不可能的,发现需要一步induction来得到t的性质*)
```

## Typing

类型正确（well-typed）定义：可由下面推到规则得到的prop

类型关系写作` |-- t \in T `读作t具备类型T

`|--`是turnstile

注意我们要标明每个参数的具体类，如succ和pred

注意这里表示最终类型推断的结果


```coq

---------------(T_True)  
|-- true ∈ Bool	

---------------------(T_False)  
|-- false ∈ Bool	

|-- t1 ∈ Bool    |-- t2 ∈ T    |-- t3 ∈ T	
------------------------------------    (T_If)  
|-- if t1 then t2 else t3 ∈ T	

----------------------  	(T_0)  
|-- 0 ∈ Nat	

|-- t1 ∈ Nat
------------------	(T_Succ)  
|-- succ t1 ∈ Nat	

|-- t1 ∈ Nat	
-----------------------(T_Pred)  
|-- pred t1 ∈ Nat	

|-- t1 ∈ Nat	
------------------------------(T_Iszero)  
|-- iszero t1 ∈ Bool	
```

```coq
Reserved Notation "'|--' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool

where "'|--' t '\in' T" := (has_type t T).
```

### Canonical forms

typing relation和bool、nat的定义是一致的

```coq
Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.

(*思路：destruct之后找矛盾就好了*)
```


### 进展性Progress

类型正确（well-typed）的式子不会被卡住

每个类型正确的程序要么是值，要么还能继续step规约

下面的证明需要理清到底用不用约简，一个陷阱就是上面说过的pred一定不是值，可以约简

```coq
Theorem progress : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
Proof. 
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, are eliminated immediately by auto *)
  - (* T_If *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (<{ if t1' then t2 else t3 }>). auto.
  - destruct IHHT.
    + left.
      apply nat_canonical in H; try assumption. auto.
      (*
      inversion H; subst.
      * right. constructor. assumption.
      * right. constructor. assumption.
      *)
    + right.
      destruct H as [t' H].
      exists <{succ t'}>.
      apply ST_Succ. assumption.
  - right.
    destruct IHHT.
    + apply nat_canonical in H; try assumption.
      destruct H.
      * eauto.
      * eauto.
    + destruct H as [t' H]. 
      exists <{pred t'}>.
      auto.
  - destruct IHHT.
    + right.
      apply nat_canonical in H; try assumption.
      destruct H.
      * exists <{true}>.
        auto.
      * exists <{false}>.
        apply ST_IszeroSucc. assumption.
    + right.
      destruct H.
      eauto.
Qed.
```

### 保类型Type Preservation

类型正确的式子step一步后还是**同类型**的类型正确式

```coq
Theorem preservation : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
(*
证明过程要用到
Example succ_hastype_nat__hastype_nat : forall t,
  |-- <{succ t}> \in Nat ->
  |-- t \in Nat.
  *)
(*
也可以对式子式子规约做induction，这样配合eauto更简单
*)

Theorem preservation' : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof with eauto.
  intros t t' T H1 H2.
  generalize dependent T. (*REVIEW*)
  induction H2;
  intros T H1;
  try (inversion H1; subst; clear H1; eauto ).
  apply succ_hastype_nat__hastype_nat.
  assumption.
Qed.
```

这个定理也叫subject reduction,表明当类型主词（subject）如何规约；

把式子看作主词，把类型看作谓词。

### Type Soundness

类型正确的式子绝不可能stuck

```coq
Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; unfold stuck; intros [R S].
  - apply progress in HT. destruct HT.
    + apply S. assumption.
    + (*normal form与进展性矛盾 *) unfold step_normal_form in R. apply R in H. inversion H.
  - apply IHP.
    + apply preservation with (t := x); assumption.
    + unfold stuck. split; assumption.
Qed.
```