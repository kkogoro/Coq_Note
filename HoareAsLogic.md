# HoareAsLogic

## 证明技巧

选定某个goal

```coq
1: {

}
```

选定所有goal

```coq
all: {
    
}
```

## 准备工作

### 命题

先搞出命题

```coq
Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable (Q [V |-> a]) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable Q d R -> derivable P c Q -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassertion b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassertion b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassertion b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassertion b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
```

```coq
Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (forall st, P st -> P' st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.
```

### 中间断言

使用最弱前条件构造

#### 定义

```coq
Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.
```

`wp c Q st`表示`st`是`wp(c, Q)`

#### 性质

```coq
Theorem wp_is_precondition : forall c Q,
  {{wp c Q}} c {{Q}}.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} ->
    P' ->> (wp c Q).
```

#### 定理

```coq
Lemma wp_seq : forall P Q c1 c2,
    derivable P c1 (wp c2 Q) -> derivable (wp c2 Q) c2 Q -> derivable P <{c1; c2}> Q.
```

`wp(while b do c end, Q)`是循环不变式

```coq
Lemma wp_invariant : forall b c Q,
    valid (wp <{while b do c end}> Q /\ b) c (wp <{while b do c end}> Q).
Proof.
  intros b c Q.
  unfold valid.
  intros st st' H1 [Hwp1 Hst].
  intros st'' H.
  unfold wp in Hwp1.
  apply Hwp1.
  eapply E_WhileTrue; eauto.
Qed.
```

### 后条件True的霍尔三元组一定可以推出

要注意的点是任何前条件都可以推出True后条件

当有一个goal最后一个是True时（可能含有形如`[X |-> a]`的sub），直接`assertion_auto''`秒了，不用管前面的假设

比如`forall st : state, P st -> ((assert_of_Prop True) [x |-> a]) st` 直接assertauto秒了

```coq
Theorem provable_true_post : forall c P,
    derivable P c True.
Proof.
  induction c; intros.
  - eapply H_Consequence_post.
    + apply H_Skip.
    + intros.
      unfold assert_of_Prop.
      exact I.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + assertion_auto''.
  - eapply H_Seq; auto.
  - apply H_If; auto.
  - eapply H_Consequence.
    + apply H_While.
      apply IHc.
    + assertion_auto''.
    + assertion_auto''.
Qed.
```

### 前条件False的霍尔三元组一定可推

while中有一步很有趣的证明：用pre再展开一层False

```coq
Theorem provable_false_pre : forall c Q,
    derivable False c Q.
Proof.
  induction c; intros.
  - eapply H_Consequence_pre.
    + apply H_Skip.
    + contradiction.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + contradiction.
  - eapply H_Consequence_pre.
    + eapply H_Seq; auto.
    + contradiction.
  - eapply H_If;
    eapply H_Consequence_pre; auto;
    ( intros st [contra _];
      contradiction ).
  - eapply H_Consequence_post. 
    + apply H_While.
      apply H_Consequence_pre with (P' := (assert_of_Prop False) ).
      * apply IHc.
      * assertion_auto''.
    + assertion_auto''.
Qed.
```

## 完备性

```coq
Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
  unfold valid. intros P c. generalize dependent P.
  induction c; intros P Q HT.
  3: {
    apply H_Seq with (Q := wp c2 Q ). (*REVIEW*) 
    all : eauto.
    (*
    - apply IHc2.
      intros.
      apply H0. assumption.
    - apply IHc1.
      unfold wp.
      intros.
      apply HT with (st := st).
      + eapply E_Seq.
        * apply H.
        * apply H1.
      + assumption.
    *)
  }
  2: {
    eapply H_Consequence_pre.
    - apply H_Asgn.
    - intros st.
      eapply HT.
      apply E_Asgn.
      reflexivity.
  }
  3: {
    remember (wp_invariant b c Q) as H.
    unfold valid in H.
    eapply H_Consequence.
    - apply H_While with (P := wp <{ while b do c end }> Q ).
      apply IHc.
      apply H.
    - unfold wp.
      intros.
      apply HT with (st := st); assumption.
    - simpl.
      intros st [Hwp Hb].
      apply Hwp.
      apply E_WhileFalse.
      Search (_ <> true).
      rewrite Bool.not_true_iff_false in Hb.
      assumption.
  }
  - eapply H_Consequence_post.
    + apply H_Skip.
    + eauto.
  - eapply H_If.
    + apply IHc1.
      intros st st' Hc1 [HP Hb].
      eapply HT.
      * apply E_IfTrue; [ | apply Hc1].
        assumption.
      * assumption.
    + apply IHc2.
      intros st st' H [HP HNb].
      eapply HT.
      * apply E_IfFalse; [ | apply H].
        assertion_auto''.
        rewrite Bool.not_true_iff_false in HNb.
        assumption.
      * assumption.      
Qed.
```

## 正确性 

先在derivable上归纳，然后发现valid P c Q实际上就是hoare1中霍尔三元组unfold valid_hoare_triple的结果，直接搬过来apply

```coq
Theorem hoare_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.  
  intros.
  induction X; unfold valid.
  - apply hoare_skip.
  - apply hoare_asgn.
  - eapply hoare_seq.
    + apply IHX1.
    + apply IHX2.
  - apply hoare_if; assumption.
  - apply hoare_while. assumption.
  - eapply hoare_consequence;
    [ apply IHX | | ].
    all : unfold "->>"; assumption.
Qed.
```