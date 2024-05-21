# auto

## auto

auto策略自动搜索可以由一系列intro和apply组成的证明

可以指定搜索的深度（apply的数量），默认5

auto的搜索范围除了当前的假设，也包括常见的逻辑命题，包括eq_refl，即等价于reflexivity

`auto 1000.`

`debug auto`会展示失败的证明过程

`info_auto`可以打印auto的证明内容

`xx_auto using H` 将H加入到apply的范围中

也可以`Hint Resolve H : core`全局扩展auto的范围

`Hint Unfold def : core`全局扩展对def的unfold

`Hint Constructors c : core`允许auto使用归纳定义c的所有constructor


## Latc

```coq
Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2 (*任何目标*)
  end.
```

```coq
Ltac find_ra :=
  match goal with 
    H1 : forall st2, ?E =[ ?E3 ]=> st2 -> _ = st2,
    H2 : ?E =[ ?E3 ]=> ?E2
    |- _ => rewrite (H1 E2 H2) in *  
    (*注意这里是E2不是?E2*)
    end.  
```

H1:匹配一条假设

|-匹配目标

?E 元变量，多次出现需匹配上同样的表达式，其中同名的代表相同的变量

_ 匹配任意

=> 匹配成功后执行的策略

## eapply

在有存在变量的时候`simpl.`不会展开一些计算，需要手动`unfold`

可能是因为存在变量的type未知，可以在任意时刻`refl`给存在变量赋值，所以`simpl`趋向于保守策略