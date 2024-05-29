# Hoare1

## 约定

在这一章中，大写字母代表Imp变量，小写字母代表Coq变量

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

注意`{{P}} c {{Q}}` 实际上由`st st'` 两个自由状态和 `st=[c]=st' P st`两个假设组成

Hoare逻辑规则

```coq
      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}

      
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}


      ---------------------------- (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}

      

```

在正式的霍尔逻辑中，seq里的c2是在c1之前给出的，一半从终止状态向起始状态推

如何在Imp中实现aexp替换X

```coq
Definition assertion_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

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

需要注意Asgn的一个谬论

```coq
------------------------------ (hoare_asgn_wrong)
{{ True }} X := a {{ X = a }}
```

考虑当a为aexp `2 * X` 且 X!=0，自然没有后条件成立