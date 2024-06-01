# Hoare1

## 约定

在这一章中，大写字母代表Imp变量，小写字母代表Coq变量

```coq
Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.
Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.
```

定义如何对断言中的表达式求值

```coq
Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.
```

## 证明tips

### unfold

可能需要unfold下面这些东西(按顺序)

```coq
"->>"

assertion_sub

t_update

bassertion
```

### 策略

可能用到如下证明策略

#### simpl

```coq
simpl in *.
```

#### congruence

证明包含等式和不等式的目标。这种策略特别擅长处理那些包含等价关系的证明，能够自动解决许多常见的等式和不等式问题，自动进行一系列rewrite

We mentioned the congruence tactic in passing in Auto when building the find_rwd tactic. Like find_rwd, congruence is able to automatically find that both beval st b = false and beval st b = true are being assumed, notice the contradiction, and discriminate to complete the proof.

#### lia

```coq
lia.

(*
H: st X < 4
---
st X + 1 < 5
这种直接lia秒了

如果goal是由数字常量、数字运算符(S\pred)、乘以常数、等于和不等关系、大小关系、逻辑连词构成，则可以通过lia解决正确的goal，若失败，则goal是false
*)
```

### 命题

```coq
eqb_eq : 用于把_=?_=true转化为_=_

leb_le : 用于把_<=?_ = true转为_<=_

le_plus_minus_r_stt:
  forall n m : nat, n <= m -> n + (m - n) = m

eq_true_negb_classical: 
  forall b : bool, negb b <> true -> b = true

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) -> (*这个Q应该是True*)
  {{P}} c {{Q}}.
```

注意区分E_asgn和hoare_asgn，后者用于hoare三元组

### Ltac

```coq
assertion_auto

assertion_auto'

assertion_auto''
```

## 霍尔三元组

`{P} c {Q}`

前条件 指令 后条件

```coq
Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 90, c custom com at level 99)
    : hoare_spec_scope.
```

注意`{{P}} c {{Q}}` 实际上由`st st'` 两个自由状态和 `st=[c]=st`、 `P st`两个假设组成

Hoare逻辑规则

### skip

```coq

      -------------------  (hoare_skip)
      {{ P }} skip {{ P }}
```

### seq

```coq
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
```

在正式的霍尔逻辑中，seq里的c2是在c1之前给出的，一半从终止状态向起始状态推

### asgn

```coq

      ---------------------------- (hoare_asgn)
      {{ Q [X |-> a] }} X := a {{ Q }}
(*注意霍尔三元组是隐含forall st st'的，因此[X |-> a]更新的st实际上是forall中的st*)
```

如何在Imp中实现aexp替换X

```coq
Definition assertion_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
(*注意看定义，[X |-> a ]更新的是断言P中forall的st，是用st计算出a，再用结果更新st中的X*)
Notation "P [ X |-> a ]" := (assertion_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

(*以及asgn的证明*)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold valid_hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. assumption.  Qed.
```

证明过程可以先`unfold valid_hoare_triple.`来展开霍尔三元组

#### asgn_wrong

需要注意Asgn的一个谬论

```coq
------------------------------ (hoare_asgn_wrong)
{{ True }} X := a {{ X = a }}
```

考虑当a为aexp `2 * X` 且 X!=0，自然没有后条件成立

```coq
Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof. (*REVIEW*)
  exists <{X * 2}>.
  intros contra.
  remember (X !-> 1) as st.
  remember (X !-> 2; X !-> 1) as st'.
  unfold valid_hoare_triple in contra.
  specialize contra with (st := st).
  specialize contra with (st' := st').
  simpl in contra.
  subst.
  rewrite t_update_eq in contra.
  simpl in contra.
  assert (H : 2 = 4 -> False).
  { discriminate. }
  apply H.
  apply contra.
  - apply E_Asgn. reflexivity.
  - reflexivity.
Qed.
```

#### asgn_fwd

asgn也可以实现为从前向后推，m用于记录前条件中X的值

```coq

       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X := a
       {{fun st' => P (X !-> m ; st') /\ st' X = aeval (X !-> m ; st') a }}

```

```coq
Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inversion H; subst. clear H.
  destruct H0 as [H1 H2].
  Search t_update_shadow.
  rewrite t_update_shadow.  (*REVIEW*)
  rewrite <- H2.
  rewrite t_update_same.  (*REVIEW*)
  rewrite t_update_eq.  (*REVIEW*)
  auto.
Qed.
```

#### asn_fwd_exists

```coq
      ------------------------------------ (hoare_asgn_fwd_exists)
      {{fun st => P st}}
        X := a
      {{fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a }}
```

### consequence

首先考虑条件的强弱问题


```coq
P ->> Q

则P比Q强，例如

<{X !-> 1; Y !-> 2}> ->> <{X !-> 1}>
```

如果我们把前条件变强，后条件变弱，霍尔三元组仍然成立

另一方面，P可能与P'是逻辑上等价的，但是在coq证明过程中没有办法直接化简出它们两个相等，需要我们分出来一步分别证明等价，请看后面的`assertion_sub_example2`

```coq
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
```

实现在coq中

```coq
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
```

例子，这里coq无法看出`X < 4`与`(X < 5) [X |-> X + 1]`等价，需要我们利用consequence分离一步

```coq
Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre with (P' := (X < 5) [X |-> X + 1]).
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.
```

能用pre/post就不要用完整的consequence,否则就要有下面这种惨剧

```coq
Example assertion_sub_example2'' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence; 
  [ | | 
  try (unfold "->>", assertion_sub, t_update; simpl; intros st H; apply H)].
  - apply hoare_asgn.
  - assertion_auto.
Qed.
```

#### auto&eauto

将下面这些加入auto的unfold列表中

```coq
Hint Unfold assert_implies assertion_sub t_update : core.
Hint Unfold valid_hoare_triple : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.
```

如果证明过程只用unfold、intros和apply以及加入到core的命题，我们就能直接auto

当证明过程中需要使用apply with（eapply）时，auto无法完成证明，但是可以用eauto来证明

auto无法代替lia

#### assertion_auto

来定义一个Ltac帮助我们简化含有assertion_sub的证明

```coq
Ltac assertion_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assertion_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)
```

可以解决这样的goal，如果手工证明，思路都是unfold "->>", assertion_sub, t_update转化为forall st, ... = ...的goal，然后intros st H，再simpl in `*`把所有的map运算化简，得到线性关系，lia

```coq
assert_of_Prop True ->>
(fun st : state => Aexp_of_aexp X st = Aexp_of_nat 1 st) [X |-> 1]
(*可以auto，因为最后是1=1*)
assert_of_Prop True ->>
(fun st : state => Aexp_of_aexp X st = Aexp_of_nat 1 st) [X |-> 1]
(*不能auto，但最后是线性关系，可以lia*)
```

#### consequence练习

```coq
Example assertion_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
```

思路是

```coq
goal:   {{ X <= 5 }}  X := 2 * X {{ X <= 10 }}
-----转化为
goal1:  {{ X <= 5 }} ->> {{ X <= 10 [X |-> 2 * X] }}
goal2:  {{ X <= 10 [X |-> 2 * X] }} X := 2 * X {{ X <= 10 }}
第一个可以hoare_asgn
第二个是assertion_sub，可以assertion_auto
```

形式化证明

```coq
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.
```

用纸笔重新推导如下证明

```coq
Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  eapply hoare_seq with (Q := (X = 1)%assertion).
  (* The annotation [%assertion] is needed to help Coq parse correctly. *)
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + auto.
Qed. 
```

## condition

```coq
              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}
```

我们需要为bexp搞一个断言形式

```coq
Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof. congruence. Qed.
```

coq下的hoare_if

```coq
(*注意这里是bexp*)
Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(*
Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassertion b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassertion b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
*)
```

### assertion_auto'

加入了对bassertion的展开以及用eqb_eq重写(_=?_)=true

```coq
Ltac assertion_auto' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.
```

加入对不等式<=?的支持

```coq
Ltac assertion_auto'' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.
```

## if1

其实`P ->> Q`和`P <{skip}> Q`是等价的

一个是

```coq
forall st, P st = Q st
```

一个是

```coq
forall st st',
st =[ skip ]=> st' ->
P st = Q st.
(*而st =[ skip ]=> st'推出st = st'*)
forall st st', P st = Q st
```

注意`%assertion`的用法

```coq
Theorem hoare_if1: forall P Q (b : bexp) c,
  {{ P /\ b }} c {{ Q }} ->
  (P /\ (~b))%assertion ->> Q ->
  {{ P }} <{ if1 b then c end }> {{ Q }}.
Proof.
  unfold valid_hoare_triple.
  intros P Q b c H1 H2 st st' Hc Hp.
  inversion Hc; subst; clear Hc; eauto.
Qed.
```

或者

```coq
Theorem hoare_if1: forall P Q (b : bexp) c,
    {{ P /\ b }} c {{ Q }} ->
    {{ P /\ ~b }} <{skip}> {{ Q }} ->
    {{ P }} <{ if1 b then c end }> {{ Q }}.
Proof.
  unfold valid_hoare_triple.
  intros P Q b c H1 H2 st st' Hc Hp.
  inversion Hc; subst; clear Hc; eauto.
Qed.
```

做个证明

因为用到了` eq_true_negb_classical `所以之前的Ltac做不了

```coq
Lemma hoare_if1_good :
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof. 
  apply hoare_if1.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
  - assertion_auto''.
    destruct H as [H1 H2].
    Search (negb _ <> true).
    apply eq_true_negb_classical in H2.
    apply eqb_eq in H2.    
    rewrite H2 in H1.
    lia.
Qed.
```

## While

### 指令不变式

指令不变式：如果 `{{ P }} c {{ P }}` 则P是c的指令不变式

### 循环不变式

循环不变式：如果`c`是循环，`{{ P /\ b }} c {{P}}` ——对循环前后都成立的断言，但是P不一定在循环过程中恒成立。无论循环是否执行，P都要在c后成立：如果b为False则前条件为False，一定能推出P； 如果b为true，则循环执行，推出P

P不一定覆盖所有程序，只要保证是循环不变式就行，例如

`{{ X = 0 }}` 是 `while X = 2 do X := 1 end` 的循环不变式，因为循环永远不会被执行

下面这个例子很有趣

```coq
(*
    The program
    while Y > 10 do Y := Y - 1; Z := Z + 1 end

    admits an interesting loop invariant:

    X = Y + Z

    Note that this doesn't contradict the loop guard but neither
    is it a command invariant of

    Y := Y - 1; Z := Z + 1

    since, if X = 5,
    Y = 0 and Z = 5, running the command will set Y + Z to 6. The
    loop guard [Y > 10] guarantees that this will not be the case.
*)
```

### hoare

```coq
            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P}} while b do c end {{P /\ ~b}}
```

在coq中实现

```coq
Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* 这里需要归纳分析后续的循环过程，我们在
  st =[c]=> st'上induction，根据之前的知识我们知道induction很有可能会丢失被induction的式子，remember一下 *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.
```

证明过程中一般需要同时利用cons_pre和cons_post来把带有b的断言转换为其他断言

如果死循环，可以有任何后状态

```coq
Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
```

## 总结

```coq

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X:=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} skip {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} while b do c end {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
```