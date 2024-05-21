# Logic

## 基础类型

Prop : proposition 命题

任何命题都对应一个type，无论tf

Theorem Lemma Example的声明中都可以看到Prop

```coq
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.
```

谓词就是返回命题的函数

`=`表达式是一个返回Prop的二元函数

`n = m` 是 `eq n m` 的句法糖（使用 [Notation] 机制定义在 Coq 标准库）

## Logical Connectives

### and

`/\` 实际上是 `and A B` 的语法糖


在结论中，用split分为两个子目标

在前提中，用`destruct H as [H1 H2]` 或获得两个前提，如果H此时还处在goal中，则可直接`intros [H1 H2]`来代替destruct

其实`/\`就是constructor，需要两个参数

其中`[]`中可以使用通配符`_`省去用不到的命题`[H1 _]`


```coq
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
(*可以看出/\是右结合的*)
```


### or

`\/` 实际上是 `or A B` 的语法糖

在前提区时使用 `destruct H as [H1 | H2]` 来获得两个证明分支

在目标区时使用 `left.` 或 `right.` 来决定证明哪个子goal

### exfalso

```coq
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.  
Qed.
```

使用爆炸原理将显然不成立的goal转化为False，从而可以apply （H: ... -> False），这种H常在`not`中产生

有tactic `exfalso.` 直接将当前goal转化为`False`

destruct类型为False的前提可自动证明定理

### not

`<>`

尽早`unfold not`可能会很有帮助

```coq
(*这几个东西等价*)
x <> y
~(x = y)
not (x = y)
(x = y) -> False
```

```coq
(*这个东西多用于双重否定消除*)
P, Q: Prop
HP: P
HNA: P -> False
---
anything
---
apply HNA in HP. destruct HP.
```


```coq
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q H.
---
P, Q: Prop
H: P \/ Q -> False
(*GOAL*)
(P -> False) /\ (Q -> False)
---
  split.
  - intros HP. apply H. left. apply HP.
  - intros HQ. apply H. right. apply HQ.
Qed.
```

### iff

```coq
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
```

`P <-> Q`  =  `iff P Q`

在前提区时，由于实质上是 `/\` ，可以用 `[HP HQ]` 构造为两个前提

在目标区时，可以使用split分为两个方向的子目标
 
对于
`b=true` 和 `b=false` 在两个命题中的情况，`rewrite`然后`discriminate`

apply一个`P<->Q`时，Coq会自动判断应用哪个方向，不需要拆成两个命题

但是注意不能直接应用在`Q->...`的goal上，必须先将Q`intros`出来

## setoid

具备 满足`reflexive` `symmetric` `transitive`的关系 的集合

这种集合可以直接使用rewrite来文本替换 关系符号 两侧的元素

```coq
mul_eq_0
  	: forall n m : nat, n * m = 0 <-> n = 0 \/ m = 0

n, m, p: nat
---
n * m * p = 0 <->
n = 0 \/ m = 0 \/ p = 0
```

此时`rewrite mul_eq_0` 将自动把`mul_eq_0`中的n替换为`n*m` (乘法左结合)

得到

```coq
n * m = 0 \/ p = 0 <->
n = 0 \/ m = 0 \/ p = 0
```

## exists

### 在前提区

```coq
(*goal*)
forall n : nat,
(exists m : nat, n = 4 + m) ->
exists o : nat, n = 2 + o
(*Proof*)
intros n [m Hm]
(*result*)
n, m: nat
Hm: n = 4 + m
---
exists o : nat, n = 2 + o
```

如果直接把`exists x, P` destruct，将会得到`P`命题，其中`m`已被特化绑定

当然也可以先`intros n H`得到`sH: exists m : nat, n = 4 + m` ， 再 `destruct H`

前提中的`exists`一定要`destruct`出来

如果`exists`是在前提中被推出的，如`H:...->exists x P`，则需要先把`exists`的前提证出来才能destruct

`exists x P`也可以直接`intros [x P]`来省掉destruct


### 在目标区

```coq
n, m: nat
Hm: n = 4 + m
---
exists o : nat, n = 2 + o
(*proof*)
exists (2 + m).
(*result*)
n, m: nat
Hm: n = 4 + m
---
n = 2 + (2 + m)
```

利用`exists x`将目标中的exists变量特化为`x`，改变goal继续证明。


```coq
(*goal*)
(exists x : X, P x \/ Q x) ->
(exists x : X, P x) \/
(exists x : X, Q x)

(*proof*)
intros [x [HP | HQ]].
```

```coq
(*goal*)
(exists x : X, P x) \/
(exists x : X, Q x) ->
exists x : X, P x \/ Q x

(*proof*)
intros [ [x HP] | [x HQ] ].
```

被exists保护的contra不能直接dicriminate，需要先destruct.

例如：

```coq
(exists x : nat, 0 = S (n + x)) ->
false = true
```

## 递归定义命题

一个特性:当某个分支前提为False时，可以`intros []`直接消除这个分支

## 为命题传参

## 常用命题

```coq
eqb_eq
  	: forall n1 n2 : nat, (n1 =? n2) = true <-> n1 = n2
```

用于处理前提`(a =? b) = true` 或 目标`(n1 =? n1)=true`



## functional_extensionality

```coq
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.
```

```coq
apply functional_extensionality.
```

```coq
Print Assumptions H
(*可以打印定理H是否依赖其他  公理  Axiom*)
```