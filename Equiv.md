# Equiv


## state用法

```coq
t_update_same :
    forall (A : Type) (m : total_map A) (x : string), (x !-> m x; m) = m
```

```coq
x : string
a : aexp
st : state
(*state是total map，将string映为Nat的函数，可以直接st x得到nat，a是aexp需要用aeval借助st中的状态计算出nat*)
Hx : st' =[ x := a ]=> (x !-> (aeval st' a) ; st').
Hx : st' =[ x := x ]=> (x !-> st' x ; st').
```

## Behavioral Equivalence 行为等价

两个命令行为等价当且仅当对于所有起始state，执行后得到的state'都相同或都没有结束state'

two commands are behaviorally equivalent if, for anygiven starting state, they either (1) both diverge or(2) both terminate in the same final state.

```coq
Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

    (** We can also define an asymmetric variant of this relation: We say
    that [c1] _refines_ [c2] if they produce the same final states
    _when [c1] terminates_ (but [c1] may not terminate in some cases
    where [c2] does). *)

Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').
```

请注意这几种关系都可以在证明等式/等价时**rewrite**! 注意cequiv在证明命题时可以apply

证明都需要split

证明cequiv需要instros两个状态st st'

`aequiv` `bequiv` `cequiv`后面接的两个可以用rewrite互相替代

`H: st =[ (c1; c2); c3 ]=> st'`等价于`H: ceval (CSeq (CSeq c1 c2) c3) st st'`

```coq
Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. discriminate.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.
```

一些重要的com上的行为等价

```coq
Theorem if_true: forall b c1 c2,
  bequiv b <{true}>  ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.

Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.

Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
```

### 一些策略

#### st =[ x:=a ]=> st

在证这种东西时，注意右面也是st，无法直接apply E_Asgn，需要将右面的东西assert

```coq
 st =[ X := a ]=> (X !-> (aeval st a) ; st)
```

然后再用E_Asgn展开

## Properties of Behavioral Equivalence


### 行为等价是等价关系

Behavioral Equivalence是自反的、传递的、对称的

选看一个证明

```coq
Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.
```

### 行为等价是同余关系 Congruence

如果子部件都满足该关系，则父部件也满足

```coq
                 aequiv a a'
         -------------------------
         cequiv (x := a) (x := a')


              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;c2) (c1';c2')
```

直觉：证明负担取决于对等式两边change的大小，而不是程序的大小，这样我们每次只改变程序的一小部分

对应的定理：可以省去intros,symmetry

```coq
Lemma refl_aequiv : ∀ (a : aexp),
  aequiv a a.

Lemma sym_aequiv : ∀ (a1 a2 : aexp),
  aequiv a1 a2 → aequiv a2 a1.

Lemma trans_aequiv : ∀ (a1 a2 a3 : aexp),
  aequiv a1 a2 → aequiv a2 a3 → aequiv a1 a3.

Lemma refl_bequiv : ∀ (b : bexp),
  bequiv b b.

Lemma sym_bequiv : ∀ (b1 b2 : bexp),
  bequiv b1 b2 → bequiv b2 b1.

Lemma trans_bequiv : ∀ (b1 b2 b3 : bexp),
  bequiv b1 b2 → bequiv b2 b3 → bequiv b1 b3.

Lemma refl_cequiv : ∀ (c : com),
  cequiv c c.

Lemma sym_cequiv : ∀ (c1 c2 : com),
  cequiv c1 c2 → cequiv c2 c1.

Lemma trans_cequiv : ∀ (c1 c2 c3 : com),
  cequiv c1 c2 → cequiv c2 c3 → cequiv c1 c3.

```

## 策略

### remember

不同于inversion（产生两个goal），直接对derivation `H: st =[ while b do c end ]=> st'` 进行induction并不会对应并去除不匹配的中间指令的constructor(产生7个goal)，并且直接induction会丢失中间指令，我们要remember中间指令的值，用于后面discriminate

```coq
Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  intros b b' c c' Heqbv Heqcv st st'.
  split.
  - 
    intros H.
    (*H: st =[ while b do c end ]=> st'*)
    remember <{ while b do c end }> as while_def.
    induction H;
    try discriminate.
```

当要证十分对称的`<->`定理时，可以assert一个方向，再apply到另一个方向，另一个方向可能要sym一下

```coq
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  assert(
          Hx: forall c1 c1' c2 c2' st st' , 
            cequiv c1 c1' -> cequiv c2 c2' -> 
            st =[ c1;c2 ]=> st' -> st =[ c1';c2' ]=> st' 
        ).{ ... }
  intros. split;
  apply Hx;
  try assumption;
  apply sym_cequiv;
  assumption.
Qed.
```

## Program Transformations

输入一段程序，输出一段程序

如果保证行为等价，就是sound的

```coq
Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).
```

### Constant folding 常量传播

#### 定义

```coq
Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.
```

```coq
Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.
```

注意if和while的常量传播写法

```coq
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }> (*这里是因为没有定义break*)
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.
```

#### soundness

```coq
Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
```

考虑下面证明的这个分支，由于fold_constants_aexp_sound的等式两边都是被`aeval st`包裹的，因此不能替换`fold_constants_aexp a1`，考虑从等式左侧把`a`变换为`fold_constant_aexp a`

```coq
Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
    - (* BLe *)
    simpl. 
    destruct (fold_constants_aexp a1) eqn:E1;
    destruct (fold_constants_aexp a2) eqn:E2;
    ( simpl; rewrite fold_constants_aexp_sound;
      rewrite fold_constants_aexp_sound with (a := a2);
      rewrite E1;
      rewrite E2;
      simpl
    ) ;
    try reflexivity.
    destruct (leb n n0) eqn:E3; reflexivity.
```

证明程序com等价时，使用行为等价的同余关系证明各部件等价！

## Proving Inequivalence

证明不等价，反证法，假设~contra中的contra成立推false，先实例化一对可能失败的程序，替换到contra命题中，然后取定起始状态`st`，分别得到两个程序的输出`st'1` `st'2`，利用contra得出这两个本不想等的state相等，推出矛盾

```coq
Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.
  (*实例化一对可能失败的程序*)
  remember <{ X := X + 1;
              Y := X }>
      as c1.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra). (*这里可以直接apply*)
  clear Contra. 

  (* 取定起始状态empty_st *)
  (* 取定终止状态st1 st2 *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Asgn; reflexivity).
  clear Heqc1 Heqc2.

  apply H in H1.
  clear H.

  (* 得到st1 = st2 *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  clear H1 H2.
  (* 利用st1 Y = st2 Y推出矛盾 *)
  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.
```
