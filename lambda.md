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

含义是把 $t_2$ 作为参数传给 $(\lambda x.t_{12})$ ，函数做的事情是把函数体 $t_{12}$ 中的 x 都替换成 $t_2$

### Church Boolean

$$
tru = \lambda t. \lambda f.t\\
fls = \lambda f. \lambda t.f
$$

含义是传入两个constructor `t` 和 `f` 分别代表true 和 false ，返回对应的的constructor

函数举例

$$
test = \lambda I. \lambda m. \lambda n. \space I \space m \space n
$$

$I$ 是bool，m n分别对应true和false时执行的语句

先读入三个constructor I、m、n，然后将m n传作I的参数

例如，当I是true时，得到的是

$$
test = [t \mapsto m, f \mapsto n] t\\
= m
$$

类似的，可以定义and

$$
\lambda a.\lambda b. \space a \space b \space fls
$$

### Church number

自然数：

$$
c_0 = \lambda s. \lambda z. z\\
c_4 = \lambda s. \lambda z. s \space (s (s (s (z))))
$$

定义函数

$$
\begin{align*}
succ &= \lambda n .\lambda s .\lambda z . s\space  (n \space s \space z) \\

plus &= \lambda n . \lambda m. \lambda s . \lambda z . \space n \space s \space (m \space s \space z) \\

times &= \lambda m. \lambda n. \space m \space (plus\space n) \space c0
\end{align*}
$$

其中n为自然数

运算过程，以times为例

$$
\begin{align*}
times \space c1 \space c2
 &=\lambda m. \lambda n. (\space m \space (plus\space n) \space c0) \space c1 \space c2 \\&=
 c1\space (plus \space c2) \space c0\\&=
    (\lambda s. \lambda z. s\space z)\space (plus \space c2) \space c0\\&=
    (plus \space c2) (c0)\\&=
    (\lambda n . \lambda m. \lambda s . \lambda z . \space n \space s (m \space s \space z)) \space c2 \space c0\\&=
\lambda s . \lambda z . (c2\space  s(c0 \space s\space  z)) \\&=
\lambda s . \lambda z . (c2\space  s\space z)\\&=
\lambda s.\lambda z . s(s(z))
\end{align*}
$$

### Y Combinator

$$
Y = \lambda f.(\lambda x. f(x\space x)) (\lambda x.f(x\space x))
$$

作用是

Y f = f (Y f)