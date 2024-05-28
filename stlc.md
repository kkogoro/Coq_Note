# Simple Typed Lambda Calculus

## overview

### 语法

```coq
 t       ::= x                         (variable)
           | \x:T,t                    (abstraction)
           | t t                       (application)
           | true                    (constant true)
           | false                  (constant false)
           | if t then t else t        (conditional)
```

注意abstraction就是函数，An abstraction $\lambda x.t$ denotes an anonymous function that takes a single input x and returns t

`\x:T,t`就是 $\lambda x.t$

和lambda部分的lambda calculus规则基本一致

### 类型

要么是bool，要么是函数

```coq
T ::= Bool
    | T -> T
```

在coq中实现

```coq
(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

(** We need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
```

值得注意的是`S -> T`右结合，`x y`(app，指的是任何可能的结合，比如函数和函数，函数和参数) 左结合，`\x : t , y` 左结合

没有类型推导，所以必须标明参数类型T

`\x:T,t`

```coq
Notation idB :=
  <{\x:Bool, x}>.

Notation idBB :=
  <{\x:Bool->Bool, x}>.

Notation idBBBB :=
  <{\x:((Bool->Bool)->(Bool->Bool)), x}>.
Notation k := <{\x:Bool, \y:Bool, x}>.

Notation notB := <{\x:Bool, if x then false else true}>.
```

## 操作语义

定义小步法语义，暂时不能实现alpha renaming，我们只考虑beta reduction

### Values

true和false显然是值，if语句不是值

在coq中，我们认为函数`\x:T, t`总是值，无论`t`是否被约简至最简

```coq
Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.
```

封闭的（没有自由变量的）语句称为完整的程序

有自由变量的叫open term

Having made the choice not to reduce under abstractions, we don't need to worry about whether variables are values, since we'll always be reducing programs "from the outside in," and that means the step relation will always be working with closed terms.

### 替换Substitution

没啥新东西，和lambda一样

`[x:=s]t` ：在t中把x替换为s

`[x:=true] (\y:Bool, if y then x else false)` yields `\y:Bool, if y then true else false`

变量作用域问题：注意 `[x:=true] (\x:Bool, x)` 并不代表着`(\x:Bool,true)` ，因为函数内的x是新变量，在这里替换规则直接失效，但如果是另一个变量y，则会继续在函数体内替换。

```coq
(** Here is the definition, informally...

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T, t)       = \x:T, t
       [x:=s](\y:T, t)       = \y:T, [x:=s]t         if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3) =
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)
```

在coq中实现

```coq
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).
```

别忘了`destruct (eqb_spec  x s0) as [H1 | H2].`的用法：
对于 `(x =? s0)%string` 可以直接得到 `x = s0` 和 `(x =? s0)%string=true` 两个命题（或 false的情形）

给出step的关系定义法：

```coq
Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tm_var x) s
  | s_var2 :
      forall y, x <> y -> substi s x (tm_var y) y
  | s_app1 :
      forall T t1, substi s x (<{\x:T, t1}>) (<{\x:T, t1}>)
  | s_app2 :
      forall y T t1, x <> y -> substi s x (<{\y:T, t1}>) (<{\y:T, [x:=s] t1}>)
  | s_tt :
      forall t1 t2, substi s x (<{t1 t2}>) ( <{([x:=s] t1) ([x:=s] t2)}>)
  | s_T :
      substi s x <{true}> <{true}>
  | S_F :
      substi s x <{false}> <{false}>
  | S_if :
      forall t1 t2 t3, substi s x <{if t1 then t2 else t3}>  <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
.
```

证明关系和函数的等价性

```coq
Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
Proof.
  intros s x t t'.
  split.
  - intros H.
    destruct t.
    + inversion H.
      destruct (x =? s0)%string eqn:E.
      * apply eqb_eq in E.
        rewrite E.
         simpl. rewrite eqb_refl.
         auto.
      * simpl.
        rewrite E.
        apply s_var2.
        apply eqb_neq.
        assumption.
    + rewrite <- H.
      auto.
    + rewrite <- H.
      (*可以用eqb_spec做得更简单！
      destruct (eqb_spec  x s0) as [H1 | H2].
      * rewrite H1. simpl. rewrite eqb_refl.
        auto.*)
      destruct (x =? s0)%string eqn:E.
      * simpl.
        rewrite E.
        apply eqb_eq in E.
        rewrite E.
        auto.
      * simpl. 
        rewrite E.
        apply s_app2.
        apply eqb_neq in E.
        assumption.
    + rewrite <- H.
      auto.
    + rewrite <- H.
      auto.
    + rewrite <- H.
      auto.
- apply substi_correctR.
Qed.  

Theorem substi_correctR : forall s x t t',
  substi s x t t' -> <{ [x:=s]t }> = t' .
Proof.
  intros.
  inversion H; subst; clear H;
  try (simpl; rewrite eqb_refl; reflexivity);
  try (simpl; apply eqb_neq in H0; rewrite H0; reflexivity);
  reflexivity.
Qed.
```

### reduction

beta reduction

先化简左侧（app是左结合的，(((()))) t2），再化简右侧

```coq
value v2
-----------------(ST_AppAbs)  
(\x:T2,t1) v2 --> [x:=v2]t1

t1 --> t1'
---------------(ST_App1)  
t1 t2 --> t1' t2

value v1
t2 --> t2'
-----------------(ST_App2)  
v1 t2 --> v1 t2'


------------------------  (ST_IfTrue)  
(if true then t1 else t2) --> t1

--------------  (ST_IfFalse)  
(if false then t1 else t2) --> t2

t1 --> t1'
-------------------------(ST_If)  
(if t1 then t2 else t3) --> (if t1' then t2 else t3)

```

```coq
Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{[x:=v2]t1}>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
```

```coq
<{(\ x : Bool -> Bool, x) 
(\ x : Bool, if x then false else true) true }> 
-->  ?y
----
(*此时应该采用app1，因为(\ x : Bool -> Bool, x) 
(\ x : Bool, if x then false else true)合在一起是左部函数*)


<{ \ x : Bool, if x then false else true }>
(*这个也是value，要把右面看作函数 v_abs*)

((\ x : Bool, if x then false else true) true)

(*这个不是value，因为不是函数而是函数调用*)
```

### alpha renaming

先思考如下app的推导:

```coq
(*可能引起误解的推导*)
(\x, (\y, x)) y
= [x := y] (\y x)
= (\y y)
(*看似得到了一个ID函数，但实际上这两个y不是同一个y，根据alpha renaming，我们的(\x, (\y, x))应该等价于(\x, (\z, x))，所以要想看到真实语义，需要让每个不同的变量名都彼此区分*)
(*正确的语义*)
(\x, (\z, x)) y
= [x := y] (\z x)
= (\z y)
```

再考虑，如果不把化简完成的函数体看成value，而是允许继续推导： 即 去掉v_abs，并加入规则

```coq
t1 -> t1'
----------------------------------
(\x : T, t1) -> (\x : T, t1')
```

就会出现不符合lambda calculus alpha renaming语义的问题：

比如

```coq
f := \y:Bool, ((\x:Bool, (\y:Bool, x)) y)

(*正确的推导应该是*)

forall z, f z = \y:Bool, ((\x:Bool, (\y:Bool, x)) y) z
              = (\x:Bool, (\y:Bool, x)) z
              = (\y:Bool, z)

(*therefore,*)
f = \z:Bool (\y:Bool,z)

(*但如果允许化简函数体，直接对函数体执行字符串替换，就会变成*)
f := \y:Bool, ((\x:Bool, (\y:Bool, x)) y)
   =(*化简函数体*) \y:Bool, ([x := y](\y:Bool, x))
   =(*作用域*) \y:Bool, (\y:Bool, y) 
   (*这里在coq的语义下就出问题了，这几个y会被coq看作同一个y，但是根据alpha renaming 实际上应该等价于\y:Bool, (\z:Bool, y) *)
(*这里按照app语义，其实等价于*) 
   = \z:Bool, (\y:Bool, y)

(*仔细对比，会发现符合lambda calculus的语义是返回第一个参数，而错误定义出的是返回第二个参数*)

```

### typing

引入上下文系统Gamma来记录变量与类型的对应关系map

`Gamma |-- t \in T` : `term t has type T, given the types of free variables in t as specified by Gamma`

`x ⊢> T ; Gamma` ： `update the partial map Gamma so that it maps x to T,`

```coq
Definition context := partial_map ty.
```

#### 类型推断规则

```coq
(** 
                            Gamma x = T1
                          ------------------                             (T_Var)
                          Gamma |-- x \in T1

                      (x |-> T2 ; Gamma) |-- t1 \in T1
                      ------------------------------                     (T_Abs)
                       Gamma |-- \x:T2,t1 \in T2->T1

                        Gamma |-- t1 \in T2->T1
                          Gamma |-- t2 \in T2
                         ----------------------                          (T_App)
                         Gamma |-- t1 t2 \in T1

                         -----------------------                         (T_True)
                         Gamma |-- true \in Bool

                         ------------------------                       (T_False)
                         Gamma |-- false \in Bool

    Gamma |-- t1 \in Bool    Gamma |-- t2 \in T1    Gamma |-- t3 \in T1
    -------------------------------------------------------------------    (T_If)
                  Gamma |-- if t1 then t2 else t3 \in T1

    We can read the three-place relation [Gamma |-- t \in T] as:
    "under the assumptions in Gamma, the term [t] has the type [T]." *)
```

这里只有`=`是读取map，`|--`是指推导出

```coq

Reserved Notation "Gamma '|--' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |-- t1 \in T1 -> (*这么写是因为有可能t1 = x*)
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.
```


```coq
Example typing_example_1 :
  empty |-- \x:Bool, x \in (Bool -> Bool).
Proof.
  apply T_Abs.
  apply T_Var.
  apply update_eq.
Qed.
```

`\x:Bool, \y:Bool, (x y)` 的结合性是`\x:Bool,  (\y : Bool, (x y))`

等价于`\x:Bool, \y:Bool, x y` ，不要管括号


```coq
assert (HT: forall T1 T2, ~(T2 = <{T2 -> T1}>)).
  { intros T1 T2 contra.
    generalize dependent T1.
    induction T2.
    - discriminate.
    - intros T1 H.
      inversion H.
      apply IHT2_1 in H1.
      destruct H1.
  }
```