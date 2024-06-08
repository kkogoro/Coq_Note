# Hoare2

## tactic

```coq
symmetry
```

## Ltac

注意这俩都是作用在霍尔三元组上的，先`outer_triple_valid`把装饰程序转换成霍尔三元组再用Ltac

### verify_assertion

之前`assertion_auto`的超级加强版，直接用

```coq
Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.
```

### verify

终极版Ltac，直接秒了

遇事不决verify一下就完事了

```coq
(** To automate the overall process of verification, we can use
    [verification_correct] to extract the verification conditions, use
    [verify_assertion] to verify them as much as it can, and finally tidy
    up any remaining bits by hand.  *)
Ltac verify :=
  intros;
  apply verification_correct;
  verify_assertion.
```

## Formal Decorated Programs

### 语法

decorated commands, or dcoms.

在每一个语句dcom后面加上后条件P

```coq
Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).
```

```coq
Example dec0 : dcom :=
  <{ skip {{ True }} }>.
Example dec1 : dcom :=
  <{ while true do {{ True }} skip {{ True }} end {{ True }} }>.
```

#### 将dcom转为com

```coq
Fixpoint erase (d : dcom) : com :=
  match d with
  | DCSkip _           => CSkip
  | DCSeq d1 d2        => CSeq (erase d1) (erase d2)
  | DCAsgn X a _       => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (erase d1) (erase d2)
  | DCWhile b _ d _    => CWhile b (erase d)
  | DCPre _ d          => erase d
  | DCPost d _         => erase d
  end.

Definition erase_d (dec : decorated) : com :=
  match dec with
  | Decorated P d => erase d
  end.

Example erase_while_ex :
    erase_d dec_while
  = <{while X <> 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.

```

#### 从dcom提取前后条件

```coq
Definition precondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq _ d2              => post d2
  | DCAsgn _ _ Q            => Q
  | DCIf  _ _ _ _ _ Q       => Q
  | DCWhile _ _ _ Q         => Q
  | DCPre _ d               => post d
  | DCPost _ Q              => Q
  end.

Definition postcondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Example precondition_from_while : precondition_from dec_while = True.
Proof. reflexivity. Qed.

Example postcondition_from_while : postcondition_from dec_while = (X = 0)%assertion.
Proof. reflexivity. Qed.
```

### Notations

```coq
Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

(** To avoid clashing with the existing [Notation]s for ordinary
    commands, we introduce these notations in a new grammar scope
    called [dcom]. *)

Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
           (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
           (in custom com at level 0, l constr at level 0,
            a custom com at level 85, P constr, no associativity)
           : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
               Pbody constr, Ppost constr)
           : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr)
           : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
          (in custom com at level 12, right associativity, P constr)
          : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
           (in custom com at level 10, right associativity, P constr)
           : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
           (in custom com at level 90, right associativity)
           : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
           (in custom com at level 91, P constr)
           : dcom_scope.

Local Open Scope dcom_scope.

```

把装饰程序转化成霍尔三元组

```coq
Definition outer_triple_valid (dec : decorated) :=
  {{precondition_from dec}} erase_d dec {{postcondition_from dec}}.

Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
Proof. reflexivity. Qed.
```

## 从装饰程序到Prop

### 转化为Prop

`verification_conditions`:生成P为dcom（缺失的）前条件的Prop

```coq
Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Q d R =>
      (* post d is both the loop invariant and the initial precondition *)
      (P ->> post d)
      /\ ((post d  /\ b) ->> Q)%assertion
      /\ ((post d  /\ ~ b) ->> R)%assertion
      /\ verification_conditions Q d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  end.
```

### 证明Prop转化是对的

```coq
Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} erase d {{post d}}.
Proof.
  (*略*)
```

```coq
Definition verification_conditions_from
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
end.

Corollary verification_conditions_correct : forall dec,
  verification_conditions_from dec ->
  outer_triple_valid dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.
```

## 证明示例

```coq
Definition if_minus_plus_dec :=
  <{
  {{True}}
  if (X <= Y) then
              {{ True /\ (X <= Y) }} ->>
              {{ Y = X + (Y - X) }}
    Z := Y - X
              {{ Y = X + Z }}
  else
              {{ True /\ ~(X <= Y) }} ->>
              {{ X + Z = X + Z }}
    Y := X + Z
              {{ Y = X + Z }}
  end
  {{ Y = X + Z}} }>.

Theorem if_minus_plus_correct :
  outer_triple_valid if_minus_plus_dec.
Proof.
  verify.
Qed.
```

注意使用ap来对imp变量应用函数

```coq
Definition parity_dec (m:nat) : decorated :=
  <{
  {{ X = m }} ->>
  {{ ap parity X = parity m }}
    while 2 <= X do
                  {{ ap parity X = parity m /\ 2 <= X }} ->>
                  {{ ap parity (X-2) = parity m }}
      X := X - 2
                  {{ ap parity X = parity m }}
    end
  {{ ap parity X = parity m /\ ~(2 <= X) }} ->>
  {{ X = parity m }} }>.
```

如果一个变量的值在循环中几乎不变，很有可能需要在条件中记录他的值

```coq
{{ X = m }} ->>                                        (a - OK)
    {{ 0 = 0*m /\ X = m }}
      Y := 0
                    {{ 0 = Y*m /\ X = m }};
      Z := 0
                    {{ Z = Y*m /\ X = m }};
      while Y <> X do
                    {{ Z = Y*m /\ X = m /\ Y <> X }} ->>   (c - OK)
                    {{ Z+X = (Y+1)*m /\ X = m }}
        Z := Z + X
                    {{ Z = (Y+1)*m /\ X = m }};
        Y := Y + 1
                    {{ Z = Y*m /\ X = m }}
      end
    {{ Z = Y*m /\ X = m /\ ~(Y <> X) }} ->>                (b - OK)
    {{ Z = m*m }}
```

自己写装饰程序并证明：别忘了seq写分号在后条件后

```coq
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (fact n')
  end.

Example factorial_dec (m:nat) : decorated :=
  <{
    {{ X = m }} ->>
                  {{ ap fact X * 1 = fact m }}
    Y := X
                  {{ ap fact Y * 1 = fact m }};
    Z := 1
                  {{ ap fact Y * Z = fact m }};
    while Y > 0 do
                  {{ ap fact Y * Z = fact m /\ Y > 0 }} ->>
                  {{ ap fact (Y - 1) * Y * Z = fact m }}
      Z := Y * Z
                  {{ ap fact (Y - 1) * Z = fact m }};
      Y := Y - 1
                  {{ ap fact Y * Z = fact m }}
    end 
    {{ ap fact Y * Z = fact m /\ ~(Y > 0)}} ->>
    {{ Z = fact m }}

  }>
.

Theorem fact_X_minus_1: forall n,
  n > 0 -> fact (n - 1) * n = fact n.
Proof.
  intros.
  destruct n.
  - lia.
  - simpl in *.
    Search (_ - 0 = _).
    rewrite sub_0_r.
    lia.
Qed.

Theorem factorial_correct: forall m,
  outer_triple_valid (factorial_dec m).
Proof. verify.
  - rewrite fact_X_minus_1; assumption.
  - assert (H1: st Y = 0).
    { lia. }
    rewrite H1 in *.
    simpl in *.
    lia.
Qed.
```

你疑似有点geek了

```coq
Definition minimum_dec (a b : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ 0 + min a b = min a b }}
      X := a
             {{ 0 + ap2 min X b = min a b }};
      Y := b
             {{ 0 + ap2 min X Y = min a b }};
      Z := 0
             {{ Z + ap2 min X Y = min a b }};
      while X <> 0 && Y <> 0 do
             {{ Z + ap2 min X Y = min a b /\ (X <> 0 /\ Y <> 0) }} ->>
             {{ (Z + 1) + ap2 min (X - 1) (Y - 1) = min a b }}
        X := X - 1
             {{ (Z + 1) + ap2 min X (Y - 1) = min a b }};
        Y := Y - 1
             {{ (Z + 1) + ap2 min X Y = min a b }};
        Z := Z + 1
             {{ Z + ap2 min X Y = min a b }}
      end
    {{ Z + ap2 min X Y = min a b /\ ~(X <> 0 /\ Y <> 0) }} ->>
    {{ Z = min a b }}
  }>.

Theorem minimum_correct : forall a b,
  outer_triple_valid (minimum_dec a b).
Proof. verify;
  try ( symmetry in H0;
        apply andb_true_eq in H0);
  [destruct H0 as [H0 _] | destruct H0 as [_ H0] | ];
  try ( symmetry in H0;
        rewrite negb_true_iff in H0;
        rewrite eqb_neq in H0;
        assumption).
  Search ((_ && _) = false).
  rewrite andb_false_iff in H0.
  unfold not.
  intros [c1 c2].
  Search (negb _ = false).
  destruct H0; [apply c1 | apply c2];
  rewrite negb_false_iff in H0;
  rewrite eqb_eq in H0;
  assumption.
Qed.
```

```coq
Definition two_loops_dec (a b c : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ 0 = 0 /\ c = 0 + c }}
      X := 0
                   {{ 0 = 0 /\ c = X + c }};
      Y := 0
                   {{ Y = 0 /\ c = X + c }};
      Z := c
                   {{ Y = 0 /\ Z = X + c }};
      while X <> a do
                   {{ Y = 0 /\ Z = X + c /\ X <> a }} ->>
                   {{ Y = 0 /\ (Z + 1) = (X + 1) + c }}
        X := X + 1
                   {{ Y = 0 /\ (Z + 1) = X + c }};
        Z := Z + 1
                   {{ Y = 0 /\ Z = X + c }}
      end
                   {{ Y = 0 /\ Z = X + c /\ ~(X <> a) }} ->>
                   {{ Z = a + Y + c }};
      while Y <> b do
                   {{ Z = a + Y + c /\ Y <> b }} ->>
                   {{ (Z + 1) = a + (Y + 1) + c }}
        Y := Y + 1
                   {{ (Z + 1) = a + Y + c }};
        Z := Z + 1
                   {{ Z = a + Y + c }}
      end
    {{ Z = a + Y + c /\ ~(Y <> b) }} ->>
    {{ Z = a + b + c }}
  }>.

Theorem two_loops : forall a b c,
  outer_triple_valid (two_loops_dec a b c).
Proof. verify. Qed.
```

很烦人的证明，其实lia都能做只是缺pow的性质

关键是

```coq
Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

Definition dpow2_dec (n : nat) :=
  <{
    {{ True }} ->>
    {{ 1 = ap pow2 0 /\  1 + 2 * 1 = ap pow2 (0 + 2) - 1 }}
      X := 0
               {{ 1 = ap pow2 X /\ 1 + 2 * 1 = ap pow2 (X + 2) - 1 }};
      Y := 1
               {{ 1 = ap pow2 X /\ Y + 2 * 1 = ap pow2 (X + 2) - 1 }};
      Z := 1
               {{ Z = ap pow2 X /\ Y + 2 * Z = ap pow2 (X + 2) - 1 }};
      while X <> n do
               {{ Z = ap pow2 X /\ Y + 2 * Z = ap pow2 (X + 2) - 1 /\ X <> n }} ->>
               {{ 2 * Z = ap pow2 (X + 1) /\ Y + 2 * Z = ap pow2 (X + 2) - 1 }}
        Z := 2 * Z
               {{ Z = ap pow2 (X + 1) /\ (Y + Z) = ap pow2 (X + 2) - 1 }};
        Y := Y + Z
               {{ Z = ap pow2 (X + 1) /\ Y = ap pow2 (X + 2) - 1 }};
        X := X + 1
               {{ Z = ap pow2 X /\ Y = ap pow2 (X + 1) - 1 }}
      end
    {{ Z = ap pow2 X /\ Y = ap pow2 (X + 1) - 1 /\ ~(X <> n) }} ->>
    {{ Y = pow2 (n+1) - 1 }}
  }>.

(** Some lemmas that you may find useful... *)

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof.
  induction n; simpl.
  - reflexivity.
  - lia.
Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof.
  induction n; simpl; [constructor | lia].
Qed.

(** The main correctness theorem: *)

Theorem dpow2_down_correct : forall n,
  outer_triple_valid (dpow2_dec n).
Proof. verify.
  - rewrite <- plus_n_O in H0.
    assert (H: st X + 2 = st X + 1 + 1).
    { lia. }
    rewrite H in H0.
    rewrite pow2_plus_1 in H0.
    rewrite <- pow2_plus_1 in H0.
    lia.
  - rewrite <- plus_n_O.
    rewrite <- pow2_plus_1.
    assert (H: st X + 2 = st X + 1 + 1).
    { lia. }
    rewrite H.
    rewrite (pow2_plus_1 (st X + 1)).
    lia.
  - rewrite <- plus_n_O.
    rewrite (pow2_plus_1 ).
    reflexivity.
  - assert(H2: st X + 1 + 1 = st X + 2).
    { lia. }
    rewrite H2.
    reflexivity.
  - Search (~ _ <> _).
    rewrite eq_dne in H1.
    rewrite H1.
    reflexivity.
Qed.
```

需要额外记录Prop:`X>=1`，用来化简fib

```coq
Definition T : string := "T".

Definition dfib (n : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ 1 = fib 0 /\ 1 = fib 0 }}
    X := 1
                {{ X >= 1 /\ 1 = ap fib X /\ 1 = ap fib (X - 1) }} ;
    Y := 1
                {{ X >= 1 /\ 1 = ap fib X /\ Y = ap fib (X - 1) }} ;
    Z := 1
                {{ X >= 1 /\ Z = ap fib X /\ Y = ap fib (X - 1) }} ;
    while X <> 1 + n do
                  {{ X >= 1 /\ Z = ap fib X /\ Y = ap fib (X - 1) /\ X <> 1 + n }} ->>
                  {{ 1 + X >= 1 /\ Z + Y = ap fib (1 + X) /\ Z = ap fib X }}
      T := Z
                  {{ 1 + X >= 1 /\ Z + Y = ap fib (1 + X) /\ T = ap fib X }};
      Z := Z + Y
                  {{ 1 + X >= 1 /\ Z = ap fib (1 + X) /\ T = ap fib X }};
      Y := T
                  {{ 1 + X >= 1 /\ Z = ap fib (1 + X) /\ Y = ap fib X }};
      X := 1 + X
                  {{ X >= 1 /\ Z = ap fib X /\ Y = ap fib (X - 1) }}
    end
    {{ X >= 1 /\ Z = ap fib X /\ Y = ap fib (X - 1) /\ ~(X <> 1 + n) }} ->>
    {{ Y = fib n }}
   }>.

Theorem dfib_correct : forall n,
  outer_triple_valid (dfib n).
Proof. verify.
  - inversion H; subst; clear H.
    + reflexivity.
    + assert(Hm: S m - 1 = m). { lia. }
      rewrite Hm.
      reflexivity.
  - rewrite sub_0_r.
    reflexivity.
  - rewrite eq_dne in H2.
    rewrite H2.
    assert(Hn: S n - 1 = n). { lia. }
    rewrite Hn.
    reflexivity.
Qed.
```

## 最弱前条件

```
[P] is a weakest precondition of command [c] for postcondition [Q]
    if

      - [P] is a precondition, that is, [{{P}} c {{Q}}]; and
      - [P] is at least as weak as all other preconditions, that is,
        if [{{P'}} c {{Q}}] then [P' ->> P].
```

### 规则

```coq
wp(c, false) = false

wp(skip, Q) = Q

wp(X := a, Q) = Q[x |-> a]

wp(c1 ; c2, Q) = wp( c1, wp(c2, Q))

wp(if b then c1 else c2 end, Q) = 
  b -> wp(c1, Q) /\ (~b) -> wp(c2, Q)

(* 等价于 *)

wp(if b then c1 else c2 end, Q) = 
  (b /\ wp(c1, Q)) \/ (~b /\ wp(c2, Q))

wp(while b do c, Q) = 
```

如果循环**至多**执行i-1次终止，

$$
\exists i>0.\space \space L_i(Q)\\  
  \text{where } L_0(Q) = \text{false}\\
  L_{j}(Q) = (\lnot b \rightarrow Q) \land (b \rightarrow wp(c, L_{j-1}(Q)))
$$

### 例子

注意(4) (5) (6)
```coq
(** **** Exercise: 1 star, standard, optional (wp)

    What are weakest preconditions of the following commands
    for the following postconditions?

  1) {{ X = 5 }}  skip  {{ X = 5 }}

  2) {{ Y + Z = 5 }}  X := Y + Z {{ X = 5 }}

  3) {{ True }}  X := Y  {{ X = Y }}

  4) {{ (X = 0 /\ Z = 4) \/ (X <> 0 /\ W = 3) }}
     if X = 0 then Y := Z + 1 else Y := W + 2 end
     {{ Y = 5 }}

  5) {{ False }}
     X := 5
     {{ X = 0 }}

  6) {{ True }}
     while true do X := 0 end
     {{ X = 0 }}
*)
```

回顾hoare1需要展开三元组的证明

```coq
Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
Proof.
  unfold is_wp.
  assert(H: {{ Y <= 4 }} <{X := Y + 1}> {{ X <= 5}} ).
  { eapply hoare_consequence_pre.
    - apply hoare_asgn.
    - verify_assertion. }
  split.
  - assumption.
  - unfold valid_hoare_triple.
    assertion_auto''.
    specialize H0 with (st := st).
    specialize H0 with (st' := (X !-> (st Y + 1); st)).
    rewrite t_update_eq in H0.
    assert(H2: st Y + 1 <= 5 -> st Y <= 4).
    { lia. }
    apply H2.
    apply H0; [| assumption].
    apply E_Asgn. auto.
Qed.
```

```coq

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) <{ X := a }> Q.
Proof.
  unfold is_wp.
  intros.
  assert (H: {{Q [X |-> a]}} <{ X := a }> {{Q}}).
  { apply hoare_asgn. }
  split.
  - assumption.
  - unfold valid_hoare_triple.
    assertion_auto''.
    specialize H0 with (st := st).
    specialize H0 with (st' := (X !-> aeval st a; st)).
    apply H0; [| assumption ].
    apply E_Asgn.
    reflexivity.
Qed.
```

## 最强后条件 

