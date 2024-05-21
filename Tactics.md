## apply

### 变量实例化

当apply eq时，eq中由forall修饰的变量会自动与利用当前goal中的变量实例化
```Coq
p: nat
eq1: forall n : nat, even n = true -> even (S n) = false
eq2: forall n : nat, even n = false -> odd n = true
eq3: even p = true
---
(1/1)
odd (S p) = true
```

此时apply eq2可自动将n替换为S p

有时复杂变量不能被正确实例化，需要apply with指明需要实例化的变量

```coq
a, b, c, d, e, f: nat
eq1: [a; b] = [c; d]
eq2: [c; d] = [e; f]
eq3: forall (X : Type) (n m o : X), n = m -> m = o -> n = o
Heqeq3: eq3 = trans_eq
---
(1/1)
[a; b] = [e; f]
```

若apply eq3，则Unable to find an instance for the variable m

需要 apply eq3 with (m:=[c\;d]). 或 apply eq3 with ([c\;d]).

### 完全匹配

apply必须完全匹配

## symmetry

交换goal的等式左右两端


## transitivity

传递性

```coq
a, b, c, d, e, f: nat
eq1: [a; b] = [c; d]
eq2: [c; d] = [e; f]
---
(1/1)
[a; b] = [e; f]
```
transitivity [c\;d].等价于用apply trans_eq with ([c\;d]).

## constructor

```coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```

injvective : 一一对应，若 S n = S m 则 n = m

disjoint : 不同constructor不相等 O != S n


## injection

对前提应用

利用constructor的单射性获取内部对应关系

```coq
n, m, o: nat
H: [n; m] = [o; o]
```

使用injection H as H1 H2.

```coq
n, m, o: nat
H1: n = o
H2: m = o
```

## f_equal

对goal应用

```coq
Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
```

有f_equal tactic，可以直接写f_equal.来自动化把goal `f[a1,a2,a3,...]=g[b1,b2,b3,...]` 转为

`f=g` `a1=b1`,`b2=b2,...`的goal

## 爆炸原理

False可以推出任何结论

## discriminate

利用constructor的disjoint

若前提等式两边constructor不同，直接推出所有命题

discriminate的参数可以省略，可以自动寻找矛盾。

```coq
n, m: nat
contra: false = true
---
(1/1)
n = m
```

discriminate contra.

Qed.

---

```coq
H: x :: y :: l1 = [ ]
---
```

discriminate H.

discriminate会自动应用simpl并自动递归到constructor深层，直到两个constructor不同

如 2 + 2 = 5会simpl为S(S(S(S(O))))=S(S(S(S(S(O))))) 然后递归到O=S(O)



## apply H1:(X->Y) in H2:(...->X)

将会在H2中把X推成Y

## specialize

特值法，可以将特定值带入条件中被全称量词forall修饰的变量，推出潜在结论

比如

```coq
n: nat
H: forall m : nat, m * n = 0
---
n=0
```

注意到m上的全称量词forall，可以`specialize H with (m:=1)` 来得到

`1*n=0->n+0=0-(add_comm)->0+n=0`

也可以用于替换系统定理加入到前提，


```coq
GOAL: [a; b] = [e; f]

trans_eq
	  : forall (X : Type) (n m o : X), n = m -> m = o -> n = o

(*如果*)
specialize trans_eq with (m:=[c;d]).
(*得到*)
GOAL: (forall n o : list nat, n = [c; d] -> [c; d] = o -> n = o) -> [a; b] = [e; f]

(*如果*)
specialize trans_eq with (m:=[c;d]) as H.
(*得到*)
H: forall n o : list nat, n = [c; d] -> [c; d] = o -> n = o
GOAL: [a; b] = [e; f]
```

当然也可以不用with直接引入系统命题e.g. specialize add_comm.


## generalize dependent

coq的特点：已经在假设区的变量不作为自由变量放入归纳假设

所以：不要将不需要归纳的变量引入假设区！

```coq
n, m: nat
---
double n = double m -> n = m
```

使用`generalize dependent n.`将n还原到goal中

```coq
m: nat
---
forall n : nat, double n = double m -> n = m
```

请注意执行后会把含有n的前提也还原进goal

请看：
```coq
n: nat
---
forall m : nat, (n =? m) = true -> n = m
```

如果对n归纳，考虑有IHn'的情况，我们的前提和goal其实都有forall m，并且两个m是独立的。

原因是显然的，因为只对n归纳了

```coq
n': nat
IHn': forall m : nat, (n' =? m) = true -> n' = m
---
forall m : nat, (S n' =? m) = true -> S n' = m
```


## unfold

Coq的simpl.只在能展开match或者展开fixpoint的时候进行约简，否则不变

同时在match的两个分支条件中含有变量的话，很可能无法看出相同，你需要unfold再对这个变量destruct


## destruct : more

可以对某个表达式destruct.

记得记录case等式，方便自己看当前讨论到哪个部分，也可用于证明

```coq
destruct (n =? 3) eqn:E1.
```

很多时候simpl不能将简单的match正确化简，需要destruct一步提示coq进行化简


destruct 后面的 `[]`内填入的实际上是constructor的参数，如对`nat`的分解应该写作

```coq
n : nat
---
destruct n as [| n']
---
(*eq to*)
destruct [|n']
```

含义是constructor `O` 或 constructor `S(n')`

因此对于`bool`，只需要写`intros []`


## induction : more

```coq
forall (l : list (X * Y)) (l1 : list X) (l2 : list Y)
---
induction l as  [| [x y] l' IHl'].
(*可将l变为(x,y) :: l' ，归纳前提命名为为IHl'
  这样写的好处是直接将复杂结构的l分的特别细致，避免后续更多destruct
  比如，如果只induction l将会展开成 x :: l'，其中x没有被细分为(x::y)，后面还要destruct
*)
```


```coq
eqb_true : forall n m : nat, (n =? m) = true -> n = m
```


## assert

```coq
assert(H:e)   (or assert(e) as H):
```

introduce a "local lemma" and call it H


## lambda表达式

```coq
(fun x => negb(test x))
```