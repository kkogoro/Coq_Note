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

这也是不能轻松做alpha renaming的原因

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

别忘了`destruct (eqb_spec  x s0) as [H1 | H2].`的用法

### reduction

beta reduction

先化简函数体，再化简参数

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

                      x |-> T2 ; Gamma |-- t1 \in T1
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

```coq
Inductive has_type : context → tm → ty → Prop :=
  | T_Var : ∀ Gamma x T1,
      Gamma x = Some T1 →
      Gamma |-- x \in T1
  | T_Abs : ∀ Gamma x T1 T2 t1,
      x ⊢> T2 ; Gamma |-- t1 \in T1 →
      Gamma |-- \x:T2, t1 \in (T2 → T1)
  | T_App : ∀ T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 → T1) →
      Gamma |-- t2 \in T2 →
      Gamma |-- t1 t2 \in T1
  | T_True : ∀ Gamma,
       Gamma |-- true \in Bool
  | T_False : ∀ Gamma,
       Gamma |-- false \in Bool
  | T_If : ∀ t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool →
       Gamma |-- t2 \in T1 →
       Gamma |-- t3 \in T1 →
       Gamma |-- if t1 then t2 else t3 \in T1

where "Gamma '|--' t '∈' T" := (has_type Gamma t T).
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

