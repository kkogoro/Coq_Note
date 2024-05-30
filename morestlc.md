# MoreSTLC

给stlc扩展更多功能，让他更像编程语言

## Num

直接加

## let

`let x=t1 in t2`

把t1规约为value，然后赋值给x（原文：给这个value起名x）

一定要先规约完t1，才能开始对let体t2的替换和规约

### 语法

```coq
 t ::=                Terms
           | ...               (other terms same as before)
           | let x=t in t      let-binding
```

### 规约规则

```coq

                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 --> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 --> [x:=v1]t2
```

### 类型推导规则

先在Gamma推出t1的类型，把这个作为先验知识添加到Gamma中再去推导出t2的类型

```coq
             Gamma |-- t1 \in T1      x|->T1; Gamma |-- t2 \in T2
             ----------------------------------------------------      (T_Let)
                        Gamma |-- let x=t1 in t2 \in T2
```

## Pairs

笛卡尔积

### 语法

```coq
       t ::=                Terms
           | ...
           | (t,t)             pair
           | t.fst             first projection
           | t.snd             second projection

       v ::=                Values
           | ...
           | (v,v)             pair value

       T ::=                Types
           | ...
           | T * T             product type
```

### 规约规则

```coq
                              t1 --> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) --> (t1',t2)

                              t2 --> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) --> (v1,t2')

                               t1 --> t1'
                           ------------------                        (ST_Fst1)
                           t1.fst --> t1'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst --> v1

                               t1 --> t1'
                           ------------------                        (ST_Snd1)
                           t1.snd --> t1'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd --> v2
```

注意，其中的v是只能指示value的元变量： The ordering arising from the use of the metavariables v and t in these rules enforces a left-to-right evaluation strategy for pairs. (Note the implicit convention that metavariables like v and v1 can only denote values.) 

同时在语法中我们指定pair的value必须两个分量都是value，这样在传作参数的时候必须先把参数pair规约完成才能开始app的规约

### 类型推导规则

```coq
              Gamma |-- t1 \in T1     Gamma |-- t2 \in T2
              -------------------------------------------              (T_Pair)
                      Gamma |-- (t1,t2) \in T1*T2

                        Gamma |-- t0 \in T1*T2
                        -----------------------                        (T_Fst)
                        Gamma |-- t0.fst \in T1

                        Gamma |-- t0 \in T1*T2
                        -----------------------                        (T_Snd)
                        Gamma |-- t0.snd \in T2
```

## Unit

`singleton type`

It has a single element -- the term constant unit (with a small u) -- and a typing rule making unit an element of Unit. 

类似Haskell和Rust的零元组`()`

### 语法

```coq
       t ::=                Terms
           | ...               (other terms same as before)
           | unit              unit

       v ::=                Values
           | ...
           | unit              unit value

       T ::=                Types
           | ...
           | Unit              unit type
```

### 类型推导规则

unit只可能是Unit类型规约的结果

```coq
                         -----------------------                       (T_Unit)
                         Gamma |-- unit \in Unit
```

Unit在现在的stlc中没啥用，但是在更加复杂，有副作用的语言中就很有用了。如果学过Rust的错误处理应该很好理解。

## Sums

`disjoint union : a set of values drawn from one of two given types`

以`Nat + Unit`为例，这个类型的值可能是Nat类型也可能是Unit类型

    实际上Nat + Unit 同构(isomorphic)于Coq的option nat

我们可以用inl和inr两个constructor来标明类型为`Nat + Unit`的元素，例如

如果`n \in Nat`，则`inl n`的类型是`Nat + Unit`；

如果`u \in Unit`，则`inr u`的类型是`Nat + Unit`。

l r代表的是后面跟着的这个元素的类型是在Sums类型的左侧还是右侧

但是在目前的STLC中，要想实现自底向上的类型推导，是没有办法只靠inl n来推断出`Nat + Unit`的，我们需要标明除了Nat以外的另一个是什么。在coq中要先传入另一半的类型才是我们上文说到的`inl`。例如 `inl Unit n` 和 `inr Nat u` 。

而为了把`inl Unit n`中的`n`取出来，我们需要实现类似Haskell中monad的东西，这里的实现方法是类似Rust的pattern match

注意，这个语法是`case ... of inl ... => ... | inr ... => ...`，这里的inl和inr是case语法的一部分而不是constructor！！！

```coq
(*这事Nat+Bool的例子*)
    getNat \in Nat+Bool -> Nat
    getNat =
      \x:Nat+Bool,
        case x of
          inl n => n
        | inr b => if b then 1 else 0
```

### 语法

```coq
       t ::=                Terms
           | ...               (other terms same as before)
           | inl T t           tagging (left)
           | inr T t           tagging (right)
           | case t of         case
               inl x => t
             | inr x => t

       v ::=                Values
           | ...
           | inl T v           tagged value (left)
           | inr T v           tagged value (right)

       T ::=                Types
           | ...
           | T + T             sum type
```

### 规约规则

x1是t1的自由变量

x2是t2的自由变量

```coq
                               t1 --> t1'
                        ------------------------                       (ST_Inl)
                        inl T2 t1 --> inl T2 t1'

                               t2 --> t2'
                        ------------------------                       (ST_Inr)
                        inr T1 t2 --> inr T1 t2'

                               t0 --> t0'
               -------------------------------------------            (ST_Case)
                case t0 of inl x1 => t1 | inr x2 => t2 -->
               case t0' of inl x1 => t1 | inr x2 => t2

            -----------------------------------------------        (ST_CaseInl)
            case (inl T2 v1) of inl x1 => t1 | inr x2 => t2
                           -->  [x1:=v1]t1

            -----------------------------------------------        (ST_CaseInr)
            case (inr T1 v2) of inl x1 => t1 | inr x2 => t2
                           -->  [x2:=v2]t2
```

### 类型推导规则

```coq
                          Gamma |-- t1 \in T1
                   -------------------------------                      (T_Inl)
                   Gamma |-- inl T2 t1 \in T1 + T2

                          Gamma |-- t2 \in T2
                   --------------------------------                     (T_Inr)
                    Gamma |-- inr T1 t2 \in T1 + T2

                        Gamma |-- t0 \in T1+T2
                     x1|->T1; Gamma |-- t1 \in T3
                     x2|->T2; Gamma |-- t2 \in T3
         -------------------------------------------------------        (T_Case)
         Gamma |-- case t0 of inl x1 => t1 | inr x2 => t2 \in T3
```

## List

为了避开多态，这里我们要在nil里传入T，同时我们用pattern match代替head和tail

### 语法

同样这里case语法中的nil是case的一部分，不是constructor

```coq
       t ::=                Terms
           | ...
           | nil T
           | cons t t
           | case t of
               nil     => t
               | x::x' => t

       v ::=                Values
           | ...
           | nil T             nil value
           | cons v v          cons value

       T ::=                Types
           | ...
           | List T            list of Ts
```

### 规约规则

xh和xt是t3中的自由变量

```coq
                                t1 --> t1'
                       --------------------------                    (ST_Cons1)
                       cons t1 t2 --> cons t1' t2

                                t2 --> t2'
                       --------------------------                    (ST_Cons2)
                       cons v1 t2 --> cons v1 t2'

                              t1 --> t1'
                -------------------------------------------         (ST_Lcase1)
                 (case t1 of nil => t2 | xh::xt => t3) -->
                (case t1' of nil => t2 | xh::xt => t3)

               ------------------------------------------          (ST_LcaseNil)
               (case nil T1 of nil => t2 | xh::xt => t3)
                                --> t2

            ------------------------------------------------     (ST_LcaseCons)
            (case (cons vh vt) of nil => t2 | xh::xt => t3)
                          --> [xh:=vh,xt:=vt]t3
```

### 类型推导规则

```coq
                        ----------------------------                    (T_Nil)
                        Gamma |-- nil T1 \in List T1

            Gamma |-- t1 \in T1      Gamma |-- t2 \in List T1
            -------------------------------------------------           (T_Cons)
                    Gamma |-- cons t1 t2 \in List T1

                        Gamma |-- t1 \in List T1
                        Gamma |-- t2 \in T2
                (h|->T1; t|->List T1; Gamma) |-- t3 \in T2
          ----------------------------------------------------         (T_Lcase)
          Gamma |-- (case t1 of nil => t2 | h::t => t3) \in T2
```

## 递归/Y组合子

正常我们在coq可以这样定义阶乘的递归函数

```coq
      let fact = \x:Nat,
             if x=0 then 1 else x * (fact (pred x)) in
      fact 3.
```

但是在我们的STLC中，有如下类型推导规则

```coq
             Gamma |-- t1 \in T1      x|->T1; Gamma |-- t2 \in T2
             ----------------------------------------------------      (T_Let)
                        Gamma |-- let x=t1 in t2 \in T2

                      (x |-> T2 ; Gamma) |-- t1 \in T1
                      ------------------------------                     (T_Abs)
                       Gamma |-- \x:T2,t1 \in T2->T1

                        Gamma |-- t1 \in T2->T1
                          Gamma |-- t2 \in T2
                         ----------------------                          (T_App)
                         Gamma |-- t1 t2 \in T1
```

可以看出要想在Gamma推出这个let的类型，就要先在Gamma中推出fact函数体的类型；想推出fact函数体的类型就要Gamma在给定`x \in Nat`时推出if语句中 x * (fact (pred x)) 的类型，而这又需要我们知道fact的类型，无法terminate了

### Y组合子

这里定义的fixed-point combinator就是lambda calculus中的Y combinator

我们这样改写fact

```coq
      fact =
          fix
            (\f:Nat->Nat,
               \x:Nat,
                  if x=0 then 1 else x * (f (pred x)))
```

在函数体中用指明类型的自由变量f代替原fact，f的类型应该和原fact一致都是`(Nat -> Nat)`，而这个abs`(\f:Nat->Nat,\x:Nat,if x=0 then 1 else x * (f (pred x)))`的类型就是`((Nat -> Nat) -> Nat -> Nat)`

此时如果把这个abs传给fix，我们就得到了一个`Nat -> Nat`的fact递归函数

而fix的规则就是fix F = F (fix F)

令`F =  (\f:Nat->Nat,\x:Nat, if x=0 then 1 else x * (f (pred x)))`，站在F的视角，f实际上处理(1..(x-1))的fact函数，而F这层就时调用第(x-1)层的计算，然后合并结果，返回x这层的计算结果

而fix f可以认为是生成了低(x-1)层计算对应的递归函数。如果我们自上而下来看(fix F) x这个计算，假设x>0，根据lambda calculus规约顺序，我们

```coq
    (fix F) x
= F (fix F) x
= (\f:Nat->Nat,\x:Nat, if x=0 then 1 else x * (f (pred x))) (fix F) x
= \x:Nat, if x=0 then 1 else x * ((fix F) (pred x)) x   (*根据T_app的替换*)
=  if x=0 then 1 else x * ((fix F) (pred x))
= x * ((fix F) (pred x))
(*此时fix F按照上文所说是生成了x - 1的计算*)
```

由于我们是一层一层规约的，(fix F)并不会直接递归得到某个函数（他的规约也不会终止），而是按需展开，如果x>0我们就展开一层(fix F)

我们可以定义多参数递归函数

```coq
    equal =
      fix
        (\eq:Nat->Nat->Bool,
           \m:Nat, \n:Nat,
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))
```

甚至成对的递归函数

```coq
    let evenodd =
         fix
           (\eo: ((Nat -> Nat) * (Nat -> Nat)),
              (\n:Nat, if0 n then 1 else (eo.snd (pred n)),
               \n:Nat, if0 n then 0 else (eo.fst (pred n)))) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)}
```

### 语法

```coq
       t ::=                Terms
           | ...
           | fix t             fixed-point operator
```

### 规约规则

```coq
                                t1 --> t1'
                            ------------------                     (ST_Fix1)
                            fix t1 --> fix t1'

               --------------------------------------------      (ST_FixAbs)
               fix (\xf:T1.t1) --> [xf:=fix (\xf:T1.t1)] t1
```

### 类型推导规则

```coq
                           Gamma |-- t1 \in T1->T1
                           -----------------------                    (T_Fix)
                           Gamma |-- fix t1 \in T1
```

现在具备了fix的STLC可以被称为PCF——"partial computable functions"

## Records

注意这里的i都是字符串，不是数字，我们不能用位置编号来访问

### 语法

```coq
       t ::=                          Terms
           | ...
           | {i1=t1, ..., in=tn}         record
           | t.i                         projection

       v ::=                          Values
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types
           | ...
           | {i1:T1, ..., in:Tn}         record type
```

### 规约规则

必须从前往后依次规约。并且在record整个规约完了才能去出他的值

```coq
                              ti --> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti , ...}
                 --> {i1=v1, ..., im=vm, in=ti', ...}

                              t0 --> t0'
                            --------------                           (ST_Proj1)
                            t0.i --> t0'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i --> vi
```

### 类型推导规则

```coq
            Gamma |-- t1 \in T1     ...     Gamma |-- tn \in Tn
          -----------------------------------------------------        (T_Rcd)
          Gamma |-- {i1=t1, ..., in=tn} \in {i1:T1, ..., in:Tn}

                    Gamma |-- t0 \in {..., i:Ti, ...}
                    ---------------------------------                  (T_Proj)
                          Gamma |-- t0.i \in Ti
```

