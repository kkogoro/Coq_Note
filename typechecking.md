# typechecking

## Comparing Types

先定义比较两个类型是否相等的函数

```coq
Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> =>
      true
  | <{ T11->T12 }>, <{ T21->T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.
```

然后把它转成命题，方便我们在证明中讨论情况的时候使用

```coq
Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
```

回顾会用到的定理

```coq
andb_true_iff:
forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true
```

## Monad

先来回顾一下Haskell的monad，方便我们进行错误处理和错误传递

作用是对给定表达式e1进行模式匹配，如果是Some y的形式，我们就取出y并给他rename成x，然后把x带入表达式e2中算出结果返回；而如果e1是None，我们就直接返回None。当然我们期望e2的返回值也是Some，这样就可以在monad层层嵌套中做好错误处理

右结合，注意e2中因为要返回一个option，所以要用return或者fail修饰

```coq
Notation " x <- e1 ;; e2" := 
                            (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e "
  := (Some e) (at level 60).

Notation " 'fail' "
  := None.
```


## The Typechecker

类型检查器接受输入Gamma和term，如果term类型正确，将会返回Some(T)，T为term的类型，否则返回None

注意Gamma的值也是option<T>

思路就是先把类型推导规则拿过来，然后对前提中的每个推导都先用monad分离出来，再做模式匹配

比如T_App

```coq
                    Gamma |-- t1 \in T2->T1
                      Gamma |-- t2 \in T2
                     ----------------------  (T_App)
                     Gamma |-- t1 t2 \in T1
```

有两个前提，我们就分别先用typechecker求出t1和t2的类型TT1和TT2，这其中任何一个类型出错都可以直接fail，得到两个类型TT1、TT2之后，观察规则发现这两个之间是有约束的，TT1必须是arrow类型(A->B)，并且arrow左侧A要和TT2相同，可以用match实现。

有了monad我们可以写的很简洁：

```coq
Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x => (*也可以写成monad*)
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2->T1}>
  | <{t1 t2}> => (*注意看这一个例子就好*)
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11->T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.
```

## checker与|--的等价性

```coq
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
```

## 扩展checker

下面我们把typechecker扩展到morestlc上

注意使用eqb_ty_refl和eqb_ty__eq

### type_check_defn

只做了sum、list和fix

```coq
Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_        => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  | <{ inl T2 t1 }> => 
      T1 <- type_check Gamma t1 ;;
      return <{{ T1 + T2 }}>
  | <{ inr T1 t2 }> => 
      T2 <- type_check Gamma t2 ;;
      return <{{T1 + T2 }}>
  | <{ case t0 of | inl x1 => t1 | inr x2 => t2}> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{T1 + T2}}> => 
          TT1 <- type_check (x1 |-> T1; Gamma) t1;;
          TT2 <- type_check (x2 |-> T2; Gamma) t2;;
          if eqb_ty TT1 TT2 then return TT1 else fail
      | _ => fail
      end
  (* lists (the [tm_lcase] is given for free) *)
  | <{ nil T }> => (*tm_nil*)
      return <{{ List T }}>
  | <{ t1::t2 }> => (*tm_cons*)
      T1 <- type_check Gamma t1 ;;
      LT2 <- type_check Gamma t2 ;;
        match LT2 with
        | <{{ List T }}> => 
          if eqb_ty T1 T then return <{{ List T }}> else fail
        | _ => fail
        end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> => (*tm_lcase*)
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{List T}}> =>
          T1 <- type_check Gamma t1 ;;
          T2 <- type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 ;;
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  (* unit *)
  (* FILL IN HERE *)
  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  | <{ fix F }> =>
    T <- type_check Gamma F ;;
      match T with
      | <{{T1 -> T2}}> => 
        if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  | _ => None  (* ... and delete this line when you complete the exercise. *)
  end.
```

### more Ltac

介绍几个`ext_type_checking_sound`命题中用于在`type_check`函数里讨论情况的Ltac

里面的H0含义直接看`ext_type_checking_sound`的证明过程，实际上就是`type_check`的计算过程模拟到了哪一步

#### solve_by_invert

```
输入一个solve次数n
匹配ProofView中，如果有命题H（和任意目标）
  H的类型是Prop， 就inversion H，
    如果n>=2就执行subst，并且递归执行solve_by_inverts(n-1)
  solve[]中包裹的内容如果最终失败，就会在ProofView中报错
```

```coq
Ltac solve_by_inverts n :=
  match goal with 
  | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        inversion H;
        match n with S (S (?n')) => 
          subst; solve_by_inverts (S n')
         end ]
    end 
  end.

Ltac solve_by_invert :=
  solve_by_inverts 1. (*这里不会subst*)
```

#### invert_typecheck

用于消除T <- type_check Gamma t的运算

讨论H0`(type_check Gamma t)`的结果(Some或None对应子结构的类型是否正确)，然后用尝试invert消除fail分支（可能消不掉，但是早晚会消掉的）。

此时应该已经可以继续推进`type_check`函数的模拟了，我们inversion一下H0并eauto推进模拟。

然后尝试subst并eauto来解决一些goal

```coq
Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
```

#### analyze

用于消除以下运算：

```coq
match T with
  | … => fail
  | <{ … }> => return …
end
```

由于T的类型是ty，直接对T进行讨论，分别对应

```coq
Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.
```

然后尝试对用inversion消除不匹配的情况

注意T1 T2是新变量命

```coq
Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.
```

#### case_equality

用于消除`if eqb_ty S T then return … else fail`

首先讨论(eqb_ty S T)是true还是false，然后可以从H0中injection出一些关系并继续模拟，根据`Heqb:(eqb_ty S T)=b`和eqb_ty__eq直接推出可以用来rewrite的`S = T`，然后不断rewrite和auto

```coq
Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.
```


#### fully_invert_typecheck

用于消除，T1 T2是新变量

```coq
T <- type_check Gamma t;;
     match T with
     | <{{ Nat }}> => return <{{ Nat }}>
     | _ => fail
     end = return T
```

```coq
Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
```

### ext_type_checking_sound

看注释吧，全写注释里了

```coq
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; (*获得term的结构*)
  intros Gamma T Htc;
  inversion Htc. 
  (*
    invert会依据结果生成函数的求值过程H0，如果destruct就会丢失H0
    H0就是直接把整个函数分支丢上去了，inversion只帮你去掉match t
    H0 : type_check Gamma t = return t
    下面我们的任务是
    1.模拟函数过程的所有分支，
    2.消除矛盾(fail分支)
    3.在可行分支中收集足够证据来证明goal
  *)
  - (*var*) 
    rename s into x. 
    (*这里H0实际上把var分成的match转化成等价的monad了*) 
    destruct (Gamma x) eqn:H. 
    (*因为monad本质是个match，我们可以对被match的Gamma x讨论*)
    rename t into T'. 
    inversion H0. (*等价于injection*)
    subst. 
    (*到此为止完成了模拟type_check函数计算过程的所有分支*)
    (*对于每个fail的矛盾分支（fail与最终结果return矛盾）*)
    (*我们都可以把他们invert掉*) 
    + apply T_Var. assumption.
    + (*fail分支*) inversion H0. 
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 TT1 TT2.
    case_equality TT1 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) apply T_Nat.
  - (* scc *)
    rename t into t1.

    invert_typecheck Gamma t1 T1.
    analyze T1 TT1 TT2.
    inversion H0...
    (*fully_invert_typecheck Gamma t1 T1 T11 T12.*)
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  (* Complete the following cases. *)
  (* sums *)
  - (* inl *)
    rename t into T2.
    rename t0 into t1.
    invert_typecheck Gamma t1 T1.  
  - (* inr *)
    rename t into T1.
    rename t0 into t2.
    invert_typecheck Gamma t2 T2.
  - (* case of sum*)
    rename s into x1.
    rename s0 into x2.
    invert_typecheck Gamma t1 T0. 
    analyze T0 T1 T2.
    remember (x1 |-> T1; Gamma) as Gamma1.
    invert_typecheck Gamma1 t2 TT1.
    remember (x2 |-> T2; Gamma) as Gamma2.
    invert_typecheck Gamma2 t3 TT2.
    case_equality TT1 TT2.
  (* lists (the [tm_lcase] is given for free) *)
  - (* tnil *)
    eauto.
  - (*x::xs*)
    rename t1 into x.
    rename t2 into xs.
    invert_typecheck Gamma x T1.
    invert_typecheck Gamma xs LT2.
    analyze LT2 LTT1 LTT2.
    case_equality T1 LTT1.
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* fix *)
    rename t into F.
    invert_typecheck Gamma F TF.
    analyze TF TTF1 TTF2.
    case_equality TTF1 TTF2.
Qed.
```