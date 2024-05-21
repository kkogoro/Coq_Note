# lambda演算

## 希尔伯特计划

是否存在一个形式系统同时满足下面的性质

1. 完备性：每个命题可以证明真假

2. 实际性：能表示自然数nat

3. 一致性：每个命题不能同时为真为假

4. 可判定性：具有一个机械的步骤可以判定所有的命题

## 哥德尔不完备

上述123不可能同时满足

## 图灵机

Turing:

## lambda calculus

Church

用函数调用定义计算

### 语法

```coq
t := terms:
    | x          变量（参数）
    | lambda x.t 函数定义
    | t t        函数调用
```

函数定义:

$$
\lambda \text{参数列表} . \text{函数体}
$$

### 语义

#### Alpha-Renaming

绑定的变量(lambda之后，`.`之前的)可以随便改名

$$
(\lambda x.x)(\lambda x.x)=(\lambda y.y)(\lambda z.z)
$$

#### Beta-Reduction

函数调用，也是唯一的计算

$$
(\lambda x.t_{12}) t_2 \rightarrow [x\mapsto t_2] t_{12}
$$

含义是把$t_2$作为参数传给$(\lambda x.t_{12})$ ，函数做的事情是把函数体 $t_{12}$ 中的 x 都替换成 $t_2$

### Church Boolean

$$
tru = \lambda t. \lambda f.t\\
fls = \lambda f. \lambda t.f
$$

含义是传入两个constructor `t` 和 `f` ，返回语义的constructor

函数举例

$$

$$