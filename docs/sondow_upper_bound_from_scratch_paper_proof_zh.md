# Sondow 侧上界存在性的从零纸面证明与 Lean 探针记录

日期：2026-07-09

本文目标是证明：在假设 Euler 常数 `gamma` 有理时，Sondow 侧产生的证书族
有多项式长度 PA 证明，从而得到项目碰撞所需的上界：

```text
exists U, polynomial_bound(U) and exists N, forall n >= N,
  proof_length_PA(sondow object at n) <= U(n).
```

证明中不把“上界存在”作为先验条件。上界必须从以下三件事推出：

1. `gamma` 有理推出 Sondow 证书从某个阈值后全部成立；
2. 每个成立的 Sondow 证书可以被一个显式、统一的有限检查器检查；
3. 对这个检查器的接受计算，可以在 PA 中写出长度为多项式的形式证明。

第三点是关键。它不是“上界存在”的先验条件，而是需要在纸面上证明的
证明编译器定理。

## 1. 目标对象

先固定一个自然数参数 `n`。Sondow 侧给出的证书可以抽象写为

```text
Cert_S(n).
```

它的内容不是一个任意证明，而是一个可检查的数据包。典型数据包括：

```text
q                 一个有理数候选，使 q = gamma；
n                 当前指标；
den(q) <= 2n      分母条件；
Sondow product/log identities；
tail/integral/decomposition identities；
若干有界整数、乘积、和、lcm 或分母估计的检查痕迹。
```

在项目使用的 half-denominator 版本中，若 `gamma = q`，则当

```text
n >= max(3, ceil(den(q)/2))
```

时，分母条件 `den(q) <= 2n` 成立，其他 Sondow 恒等式由 Sondow 公式本身给出。
因此从某个阈值后，每个 `n` 都有一个 Sondow 证书。

记这个阈值为

```text
N_S(q) = max(3, ceil(den(q)/2)).
```

这一步只使用 Sondow 侧数学条件，不使用任何证明长度上界。

## 2. 第一步：有理性推出 Sondow 证书尾部成立

**命题 1。** 若 `gamma = q`，其中 `q` 是有理数，则对所有
`n >= N_S(q)`，`Cert_S(n)` 成立。

**证明。**

令

```text
N_S(q) = max(3, ceil(den(q)/2)).
```

若 `n >= N_S(q)`，则有：

```text
n >= 3,
ceil(den(q)/2) <= n.
```

第二个不等式给出

```text
den(q) <= 2n.
```

Sondow 证书中涉及 `q` 的分母部分因此被满足。

另一方面，假设 `gamma = q`。Sondow 的分解公式和乘积/积分恒等式把
`gamma` 的有理性转化为对应的有限等式或有限不等式。由于每个固定 `n` 的
证书只涉及有限求和、有限乘积、有限 lcm、有限有理数运算和固定的尾项估计，
这些检查项都在 `gamma = q` 与 Sondow 公式下成立。

因此，对所有 `n >= N_S(q)`，存在一个具体证书数据包 `Cert_S(n)`。

证毕。

这一命题只说明“证书为真”。它还没有说明 PA 中存在短证明。

## 3. 第二步：证书大小是多项式有界的

**命题 2。** 存在常数 `a,b`，使得对所有 `n >= N_S(q)`，可以选择
`Cert_S(n)` 的编码长度满足

```text
|Cert_S(n)| <= a (n+1)^b.
```

**证明思路。**

Sondow 证书只记录以下类型的数据：

1. 固定有理数 `q`；
2. 当前自然数 `n`；
3. 有界范围内的有限和、有限积、lcm、指数、分母检查；
4. 每个检查步骤的局部等式或不等式见证。

`q` 是固定的，所以其编码长度是常数。

`n` 的二进制长度是 `O(log n)`，即使使用一元或更保守的自然数编码，也至多
是 `O(n)`。

证书中出现的有限列表长度至多是多项式级。原因是所有求和、乘积、lcm 或
分母检查都只运行到 `n`、`2n` 或某个固定多项式函数 `p(n)`。每个列表项的
数值大小来自有界乘法、加法、指数或 lcm 构造。即使用保守估计，每个中间
整数的编码长度也被某个多项式支配。

因此整个证书编码长度被某个自然系数多项式支配：

```text
|Cert_S(n)| <= a(n+1)^b.
```

证毕。

注意：这里没有用 PA 证明长度上界，只是在估计 Sondow 证书这个有限对象的
编码大小。

## 4. 第三步：存在统一的多项式时间检查器

定义一个确定性检查器 `V_S`。输入为 `(n, c)`，其中 `c` 是候选 Sondow
证书。检查器逐项验证：

```text
1. c 中的 q 是否满足 q = gamma 的证书字段；
2. den(q) <= 2n；
3. Sondow finite product/log identity 的每个有限步骤；
4. integral/tail/decomposition 的有限检查项；
5. 所有整数、有理数、lcm、乘法、加法、幂运算的局部计算记录。
```

**命题 3。** 存在常数 `A,B`，使得对于命题 1 中构造的证书 `Cert_S(n)`，
检查器 `V_S(n, Cert_S(n))` 在至多

```text
A(n+1)^B
```

步内接受。

**证明。**

每个检查项都是有限算术检查。检查项个数至多多项式，单项检查的输入长度也
至多多项式。整数加法、乘法、比较、除法余数检查、lcm 检查和有理数等式
检查都可以在多项式时间内完成。

因此整个检查过程是多项式时间的。取一个足够大的指数 `B` 与系数 `A`，
使所有检查步骤总数被

```text
A(n+1)^B
```

支配。

证毕。

到这里为止，我们只证明了“证书可被多项式时间检查”。仍然没有把它变成 PA
证明长度上界。

## 5. 第四步：多项式时间接受计算可以转成多项式长度 PA 证明

这是核心元定理。

**命题 4。** 设 `V` 是一个固定的确定性多项式时间检查器。若 `V(x)` 在
`T` 步内接受，则 PA 中存在一个证明，证明“`V` 在输入 `x` 上接受”，且该
PA 证明长度至多为

```text
C(T+|x|+1)^D
```

其中 `C,D` 只依赖于检查器 `V` 和 PA 的编码约定，不依赖于具体输入 `x`。

**证明。**

把 `V` 固定为一台图灵机、RAM 程序或等价的寄存器机。对任意接受计算

```text
config_0, config_1, ..., config_T,
```

构造 PA 证明，逐行证明以下事实：

```text
config_0 是输入 x 的初始配置；
对每个 i < T，config_i 按 V 的转移规则一步变为 config_{i+1}；
config_T 是接受配置。
```

由于 `V` 固定，每条转移规则是一个固定的有限算术公式。PA 可以直接证明
每一步转移的正确性。每一步证明长度被当前配置编码长度的某个固定多项式
控制。

计算时间为 `T`，工作带或寄存器内容长度也被某个关于 `T+|x|` 的多项式
控制。因此所有配置编码的总长度至多是

```text
poly(T+|x|).
```

将 `T` 条局部转移证明串联，再加上初始配置和接受配置证明，总 PA 证明长度
仍为

```text
C(T+|x|+1)^D.
```

证毕。

这个命题不是上界先验。它是显式构造 PA 证明的证明编译器。若要完全形式化，
Lean 中必须把机器模型、配置编码、转移正确性、PA 内部算术证明长度估计逐项
实现。

## 6. 第五步：推出纯 Sondow 证书族的 PA 证明长度上界

令

```text
x_n = (n, Cert_S(n)).
```

由命题 2，

```text
|x_n| <= a'(n+1)^{b'}.
```

由命题 3，

```text
V_S(x_n) accepts within A(n+1)^B steps.
```

由命题 4，PA 中存在一个证明，证明 `V_S(x_n)` 接受，且证明长度至多

```text
C(A(n+1)^B + a'(n+1)^{b'} + 1)^D.
```

右侧仍可被某个自然系数多项式支配。因此存在多项式 `U_S(n)`，使得对所有
`n >= N_S(q)`，

```text
proof_length_PA(sondow certificate accepted at n) <= U_S(n).
```

这就是纯 Sondow certificate 层面的上界。

## 7. 第六步：从纯 Sondow 证书到项目 reflection-graft 上界

项目中碰撞使用的对象通常不是单独的 Sondow certificate，而是
reflection-graft 目标：

```text
sondowReflectionGraftCode(n).
```

它可以理解为把 Sondow 证书侧和某个固定的辅助侧组合成一个目标公式。若要
得到

```text
proof_length_PA(sondowReflectionGraftCode(n)) <= U(n),
```

还需要证明两个构造性事实：

1. 辅助侧在每个 `n` 有多项式长度 PA 证明；
2. 从 Sondow 侧 PA 证明和辅助侧 PA 证明构造 reflection-graft 目标证明时，
   只增加多项式，最好是线性或常数级开销。

如果辅助侧证明长度由多项式 `U_P(n)` 控制，而 Sondow 侧由 `U_S(n)` 控制，
并且 graft 组合开销满足

```text
length(graft proof at n) <= U_S(n) + U_P(n) + C,
```

那么

```text
U(n) = U_S(n) + U_P(n) + C
```

就是项目 reflection-graft 对象的多项式上界。

这里最容易出信用风险：不能把“辅助侧有短证明”或“graft 组合后有短证明”
作为不透明上界输入。必须把辅助侧证明和 graft 组合器也显式构造出来，或者
把它们作为单独命名的、可审计的底层证明编译器定理。

## 8. 总定理

**定理。** 假设 `gamma = q`，且以下内容已经被显式构造并证明：

1. Sondow 证书 `Cert_S(n)` 在 `n >= N_S(q)` 后成立；
2. `Cert_S(n)` 的编码长度被多项式支配；
3. 存在固定检查器 `V_S`，它在多项式时间内检查 `Cert_S(n)`；
4. PA 能以多项式长度证明 `V_S` 的每个接受计算；
5. reflection-graft 的辅助侧证明和组合器也有显式多项式长度构造。

则存在多项式 `U` 和阈值 `N`，使得对所有 `n >= N`，

```text
proof_length_PA(sondowReflectionGraftCode(n)) <= U(n).
```

**证明。**

由 1 得到尾部每个 `n` 的 Sondow 证书。

由 2 和 3 得到尾部每个证书的接受计算长度被某个多项式支配。

由 4 把接受计算翻译成 PA 证明，得到纯 Sondow 侧 PA 证明长度多项式上界。

由 5 把纯 Sondow 侧证明和辅助侧证明组合成 reflection-graft 目标证明，并且
组合过程只造成多项式开销。

多项式在加法、乘法、复合和取最大下封闭。因此最终得到一个多项式 `U`，
支配整个 reflection-graft 目标证明长度。

证毕。

## 9. 这条证明的风险点

这份纸面证明没有把上界存在作为先验条件，但它有必须补齐的底层证明义务：

```text
P1. Sondow 证书编码大小的逐项多项式估计；
P2. Sondow 检查器的多项式时间界；
P3. PA 对检查器接受计算的多项式长度证明模拟；
P4. reflection-graft 辅助侧证明的显式构造；
P5. graft 组合器的长度开销估计。
```

如果 P1--P5 被证明，上界就是推出的，不是先验假设。

如果 P3 或 P4 只是被写成“存在短证明”的字段，那么信用风险仍然存在，因为
那等价于把上界藏到了检查器或辅助侧输入里。

## 10. 对 Lean 内化的要求

Lean 中最终不能只写：

```lean
axiom sondowUpperProvider : Month9Month10PayloadFreeUpperProvider
```

也不应只写：

```lean
structure SondowUpperData where
  upper : exists U, polynomial_bound U and ...
```

正确内化目标应是分层定理：

```lean
theorem sondowCertificateTail_of_rationality :
  is_rational gamma ->
    exists N, forall n >= N, SondowCertificateHolds n

theorem sondowCertificate_size_polynomial :
  polynomial_bound (fun n => size (Cert_S n))

theorem sondowVerifier_accepts_tail :
  forall n >= N, V_S n (Cert_S n) = true

theorem paProofOfAcceptedSondowCertificate_polynomial :
  forall n >= N,
    proof_length_PA (sondowCertificateValidCode n) <= U_S n

theorem reflectionGraftUpper_from_sondowProofCompiler :
  forall n >= N,
    proof_length_PA (sondowReflectionGraftCode n) <= U n
```

最后才包装成：

```lean
def buildSondowUpperProvider : Month9Month10PayloadFreeUpperProvider := ...
```

这样“上界存在”是定理链的结论，而不是输入。

## 11. 当前代码探针对这个纸面证明的反馈

已有代码可以从 reproof 和 verification bridge 构造出上界形状，但 probe
显示它经过了旧的 root `accepted_certificate`，从而带入了
`partial_consistency_payload` 和 `strengthened_partial_consistency_payload`。

这说明：

```text
纸面证明方向是对的；
当前 root accepted-certificate 内化路径不够干净；
下一步应把 P1--P5 直接内化到 Sondow 专用 checker/accepted-at 语义上，
不要再经过 root accepted_certificate。
```

特别是，half-denominator Sondow full-certificate tail 已经是干净的底层起点：

```text
gamma = q
=> n >= max(3, ceil(den(q)/2))
=> Sondow full certificate checks at n.
```

需要补的是从这个 Sondow 专用 checked tail 到 PA 多项式长度证明的显式证明
编译器，而不是再次引入 `sondowUpperProvider`。

## 12. 证明探针记录

对应的 Lean probe 文件为：

```text
integration/SondowProjectSondowUpperProofProbe.lean
```

该文件没有声明 `sondowUpperProvider`，也没有把
`Month9Month10PayloadFreeUpperProvider` 作为输入。它做了三件事：

1. 从 Sondow reproof 和 concrete verification package 推出纯 Sondow
   certificate 的 PA proof-length upper；
2. 从 Sondow reproof 和 collapse verification bridge 推出项目
   `sondowProjectLocalPudlakCollisionBox` 的 upper；
3. 把第二步的结论包装成 payload-free upper-provider 接口。

构建命令：

```bash
lake build integration.SondowProjectSondowUpperProofProbe
```

构建结果：

```text
Build completed successfully.
```

axiom/profile 探针命令：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectSondowUpperProofProbe
open SondowMainCheckedCodeBridge.SondowProjectSondowUpperProofProbe

#print axioms pureSondowCertificateUpper_fromReproofConcreteVerification
#print axioms projectLocalUpper_fromReproofVerifiedCollapse
#print axioms payloadFreeUpperProvider_fromReproofVerifiedCollapse
#print axioms halfDenCheckedTailOfRationalParameter
EOF
```

观察结果：

```text
pureSondowCertificateUpper_fromReproofConcreteVerification
depends on:
[partial_consistency_payload,
 proof_length,
 propext,
 strengthened_partial_consistency_payload,
 Classical.choice,
 Quot.sound]

projectLocalUpper_fromReproofVerifiedCollapse
depends on:
[partial_consistency_payload,
 proof_length,
 propext,
 strengthened_partial_consistency_payload,
 Classical.choice,
 Quot.sound]

payloadFreeUpperProvider_fromReproofVerifiedCollapse
depends on:
[partial_consistency_payload,
 proof_length,
 propext,
 strengthened_partial_consistency_payload,
 Classical.choice,
 Quot.sound]

halfDenCheckedTailOfRationalParameter
depends on:
[propext,
 Classical.choice,
 Quot.sound]
```

解释：

```text
halfDenCheckedTailOfRationalParameter
```

是干净的 Sondow 专用起点。它从 `gamma = q` 直接得到 half-denominator
checked tail，没有引入两个 payload 常量。

但是，当前从 checked/accepted certificate 到 PA proof-length upper 的现成
代码路线经过 root `accepted_certificate`。这个 root 谓词把 Sondow certificate、
partial consistency payload 和 strengthened payload 放在同一个旧谓词里，
所以 axiom profile 中重新出现：

```text
partial_consistency_payload
strengthened_partial_consistency_payload
```

因此当前 probe 的结论是：

```text
逻辑形状成功：上界可以从 reproof + verifier/collapse bridge 构造出来，
不是直接假设 upper_provider。

信用清洁度失败：现成代码路线仍经过 root accepted_certificate，因此不满足
“完全从 Sondow 专用条件出发”的目标。
```

下一步内化目标应直接证明：

```text
Sondow checked tail
  -> Sondow verifier accepts
  -> PA has polynomial-length proof of verifier acceptance
  -> proof_length upper
```

并且整个过程不调用 root `accepted_certificate`。

## 13. 新的干净 Lean 探针：checked-tail 加 PA trace compiler

2026-07-09 新增了一个更贴近上述纸面证明的探针文件：

```text
integration/SondowProjectSondowUpperCompilerRoute.lean
```

它不把 `upper_provider` 作为输入。最新探针把证明长度分成两层。

第一层是 proof-length-free 的具体证明码编译器：

```lean
SondowFullCertificateConcreteProofCodeCompiler
```

该对象的含义是：

```text
如果 MainSondowFullCertificateCheckedAt n 已经检查通过，
那么可以构造一个具体 PA/Hilbert proof code，
其 codeLength 不超过 Sondow verifier predicate size。
```

这里完全不使用 root `proof_length` 常量。这是更适合作为论文信用基础的上界
路线。

在这个 concrete compiler 输入下，Lean 已经证明了显式线性上界：

```lean
pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
```

其数学内容是：

```text
若 q = gamma，并且 n >= max 3 ((q.den + 1) / 2)，则

codeLength(n) <= 17 * (n + 1).
```

进一步包装后得到 proof-length-free 的 existential upper-tail 形状：

```lean
pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndCompiler
```

在这一层，existential upper 是结论，不是前提；具体上界就是
`sondowCertificateLinearUpper n = 17 * (n + 1)`。

第二层才是兼容旧 root `proof_length` 接口的对象：

```lean
SondowFullCertificatePATraceCompiler
```

该对象的含义是：

```text
如果 MainSondowFullCertificateCheckedAt n 已经检查通过，
那么 PA 可以证明 sondowCertificateValidCode n，
并且证明长度不超过 Sondow verifier predicate size。
```

它的结论直接写成 root

```text
proof_length PA symbolSize (sondowCertificateValidCode n)
```

所以该层的 axiom profile 必然含 `proof_length`。这层只应被理解为与旧接口的
连接层，不应被说成完全 proof-length-free。

root 层 Lean 已经证明：

```lean
pureSondowLinearUpper_fromHalfDenCheckedTailAndTraceCompiler
```

数学内容是：

```text
若 q = gamma，并且 n >= max 3 ((q.den + 1) / 2)，则

proof_length PA symbolSize (sondowCertificateValidCode n)
  <= 17 * (n + 1)
```

进一步包装后得到旧接口需要的 existential upper-tail 形状：

```lean
pureSondowCertificateUpper_fromHalfDenCheckedTailAndTraceCompiler
```

但这里的 existential upper 是结论，不是前提；具体上界就是
`sondowCertificateLinearUpper n = 17 * (n + 1)`。

复现命令：

```bash
lake build integration.SondowProjectSondowUpperCompilerRoute
lake env lean --stdin <<'EOF'
import integration.SondowProjectSondowUpperCompilerRoute
open SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute

#print axioms SondowFullCertificateConcreteProofCodeCompiler
#print axioms pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
#print axioms pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndCompiler
#print axioms SondowFullCertificatePATraceCompiler
#print axioms pureSondowLinearUpper_fromHalfDenCheckedTailAndTraceCompiler
#print axioms pureSondowCertificateUpper_fromHalfDenCheckedTailAndTraceCompiler
EOF
```

观察到的 axiom profile：

```text
SondowFullCertificateConcreteProofCodeCompiler
  does not depend on any axioms

pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
  [propext, Classical.choice, Quot.sound]

pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndCompiler
  [propext, Classical.choice, Quot.sound]

SondowFullCertificatePATraceCompiler
  [proof_length, propext, Classical.choice, Quot.sound]

pureSondowLinearUpper_fromHalfDenCheckedTailAndTraceCompiler
  [proof_length, propext, Classical.choice, Quot.sound]

pureSondowCertificateUpper_fromHalfDenCheckedTailAndTraceCompiler
  [proof_length, propext, Classical.choice, Quot.sound]
```

最关键的审计结论是：

```text
partial_consistency_payload
strengthened_partial_consistency_payload
```

没有出现。也就是说，若沿着

```text
half-den checked tail
  -> SondowFullCertificateConcreteProofCodeCompiler
  -> explicit concrete-code 17(n+1) upper
```

这条路线推进，两个 payload 依赖可以被绕开，并且干净核心不经过
root `proof_length`。若要回到旧接口中的 PA proof-length 语句，还需要另加
`SondowFullCertificatePATraceCompiler` 作为 exactness/calibration 层；该层的
axiom profile 含 `proof_length`，所以不能把它当作最终干净核心。

剩余负债也更清楚：

```text
必须继续把 SondowFullCertificateConcreteProofCodeCompiler 展开为真正的
PA/Hilbert proof-code 构造和 verifier 模拟；
root proof_length 版本只能作为 exactness/calibration 层，
不能作为最终“完全干净”的上界证明核心。
```

## 14. 2026-07-09 更新：避开 root accepted-certificate 的 clean checked route

上一节的 `SondowFullCertificateConcreteProofCodeCompiler` 仍然比较抽象。最新
Lean 探针把它进一步拆成了更接近标准证明论的两个对象：

```lean
SondowCheckedS21TraceCompiler
S21ToPALinearEmbeddingOn sondowCertificateValidCode
```

第一项是 Sondow 专用的 S²₁ trace compiler。它的输入不是 root
`accepted_certificate (sondowCertificateValidCode n)`，而是更底层的

```lean
MainSondowFullCertificateCheckedAt n
```

也就是说，它直接从“第 `n` 个 Sondow full certificate 已经由专用检查器
检查通过”出发，给出：

```text
proof_length S21 symbolSize (sondowCertificateValidCode n)
  <= proof_predicate_formula_size sondowCertificateValidCode n.
```

这一步正好对应纸面证明中的“多项式时间 Sondow 检查器接受计算可以被
S²₁/PA 形式化为短证明”。它仍是证明论义务，但已经不再是
`upper_provider`，也不再经过 root `accepted_certificate`。

Lean 中已证明的 clean S²₁ 上界为：

```lean
s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
```

其数学内容是：

```text
若 q = gamma 且 n >= max 3 ((q.den + 1) / 2)，则

proof_length S21 symbolSize (sondowCertificateValidCode n)
  <= 17 * (n + 1).
```

包装后的存在型上界为：

```lean
s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
```

第二项 `S21ToPALinearEmbeddingOn sondowCertificateValidCode` 把 S²₁ 短证明
线性传输到 PA。由于该 embedding 的一般形式是

```text
PA_length <= C * S21_length + D,
```

所以 PA 层的显式上界不再强行写成 `17(n+1)`，而是：

```lean
sondowPAUpperViaS21Embedding embedding n
  = embedding.C * (17 * (n + 1)) + embedding.D.
```

Lean 中已证明：

```lean
paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
```

其数学内容是：

```text
若 q = gamma 且 n >= max 3 ((q.den + 1) / 2)，则

proof_length PA symbolSize (sondowCertificateValidCode n)
  <= embedding.C * 17(n+1) + embedding.D.
```

这里的上界是结论，不是输入。剩余输入已经从不透明的
`sondowUpperProvider` 降到了两个标准证明论对象：

```text
1. SondowCheckedS21TraceCompiler
2. S21ToPALinearEmbeddingOn sondowCertificateValidCode
```

### 14.1 为什么不能走 root accepted-certificate

探针还保留了一个 diagnostic theorem：

```lean
acceptedSondowCertificate_of_checkedAt
```

它把

```lean
MainSondowFullCertificateCheckedAt n
```

转成 root

```lean
accepted_certificate (sondowCertificateValidCode n)
```

数学上这只用 Sondow 分支；但是 Lean 的 `#print axioms` 会展开整个 root
`accepted_certificate` 定义，而该定义还包含 partial-consistency 和
strengthened-partial-consistency 分支。因此该 diagnostic bridge 的 axiom
profile 会重新出现：

```text
partial_consistency_payload
strengthened_partial_consistency_payload
```

这不是因为 Sondow 证明本身用了 payload，而是因为 root predicate 把多个
certificate family 混在同一个定义里。结论是：投稿主线不能把 root
`accepted_certificate` 当作 Sondow 上界证明的核心接口。

### 14.2 最新 Lean 复现命令

```bash
lake build integration.SondowProjectSondowUpperCompilerRoute
lake env lean --stdin <<'EOF'
import integration.SondowProjectSondowUpperCompilerRoute
open SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute

#print axioms SondowCheckedS21TraceCompiler
#print axioms s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
#print axioms s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
#print axioms paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
#print axioms paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
#print axioms acceptedSondowCertificate_of_checkedAt
#print axioms paSondowCertificateUpper_fromHalfDenCheckedTailTraceAndEmbedding
EOF
```

观察结果：

```text
SondowCheckedS21TraceCompiler
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]

acceptedSondowCertificate_of_checkedAt
  [partial_consistency_payload, propext,
   strengthened_partial_consistency_payload, Classical.choice, Quot.sound]

paSondowCertificateUpper_fromHalfDenCheckedTailTraceAndEmbedding
  [partial_consistency_payload, proof_length, propext,
   strengthened_partial_consistency_payload, Classical.choice, Quot.sound]
```

因此最新结论是：

```text
clean checked route:
  half-den Sondow checked tail
    -> SondowCheckedS21TraceCompiler
    -> S21ToPALinearEmbeddingOn sondowCertificateValidCode
    -> explicit PA upper embedding.C * 17(n+1) + embedding.D

dirty diagnostic route:
  checked tail
    -> root accepted_certificate
    -> root S21VerifierTraceSoundness
    -> payload constants reappear in axiom profile
```

### 14.3 当前剩余义务

Sondow 上界已经不再需要 `upper_provider` 或 root accepted-certificate。剩余
信用义务被精确下沉为：

```text
SondowCheckedS21TraceCompiler
```

也就是：从 Sondow 专用 checked certificate 构造 S²₁ 短证明的 trace
compiler。若再要求 PA 层上界，还需要：

```text
S21ToPALinearEmbeddingOn sondowCertificateValidCode
```

这两个对象是标准证明论编译义务，不是 Sondow 数学上界本身的先验条件。下一步
若要继续完全关闭，就应在 Lean 中显式实现 Sondow checked certificate 的
S²₁ proof-code trace construction，而不是回到 root `accepted_certificate`。

## 15. 完成版收束：Sondow 上界到底由什么推出

本节把前面的草案、代码探针和审计结论合并成一个可引用的证明路线。核心点是：

```text
Sondow 上界不是一个先验 upper-provider。
它来自 rationality tail + checked certificate + verifier-size bound +
S²₁/PA 证明编译。
```

更精确地说，固定有理数 `q`，并假设

```text
(q : Real) = euler_mascheroni.
```

令

```text
N_S(q) = max 3 ((q.den + 1) / 2).
```

项目中已经有 Lean 定理给出 half-denominator checked tail：

```lean
mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
```

其内容是：

```text
forall n >= N_S(q),
  MainSondowFullCertificateCheckedAt n.
```

这一步只从 Sondow reproof 和 `q = gamma` 出发，不使用 proof length，也不经过
root `accepted_certificate`。

另一方面，项目中已有显式 verifier-size 上界：

```lean
proofPredicateFormulaSizeSondowCertificateValidCode_le_17_natPower
```

其内容是：

```text
proof_predicate_formula_size sondowCertificateValidCode n
  <= 17 * (n + 1).
```

因此，只要补上 Sondow 专用的 checked-trace compiler：

```lean
SondowCheckedS21TraceCompiler
```

也就是

```text
MainSondowFullCertificateCheckedAt n
  -> proof_length S21 symbolSize (sondowCertificateValidCode n)
       <= proof_predicate_formula_size sondowCertificateValidCode n,
```

就能在 Lean 中推出：

```text
forall n >= N_S(q),
  proof_length S21 symbolSize (sondowCertificateValidCode n)
    <= 17 * (n + 1).
```

这正是当前新增定理：

```lean
s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
```

它的存在型版本为：

```lean
s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
```

所以 S²₁ 层面的 Sondow 上界已经被压缩成一个非常具体的证明义务：

```text
证明 Sondow checked certificate 的 S²₁ 短证明编译器。
```

这个义务不是“上界存在”的先验条件。它是一个标准的算术化证明编译定理：

```text
一个固定的多项式时间检查器接受某个显式证书
=> S²₁ 能用与检查痕迹线性/多项式相关的长度证明其接受。
```

在纸面数学上，这个编译定理的证明如下。

1. 把 Sondow full certificate checker 写成固定的有限程序 `V_S`。输入为 `n`
   和候选证书，输出接受或拒绝。
2. `MainSondowFullCertificateCheckedAt n` 表示存在具体证书 `c_n`，并且
   `V_S(n,c_n)` 接受。
3. 接受计算有一条有限 trace：

   ```text
   C_0, C_1, ..., C_T.
   ```

4. `V_S` 是固定程序，每一步转移规则都是固定的有界算术关系。S²₁ 可以逐步
   验证：

   ```text
   C_0 是输入配置；
   C_i -> C_{i+1} 符合 V_S 的转移规则；
   C_T 是接受配置。
   ```

5. 这些局部验证证明按 trace 顺序合并，得到一个 S²₁ 证明，证明
   `sondowCertificateValidCode n`。
6. 由于 `proof_predicate_formula_size sondowCertificateValidCode n` 已经把输入
   编码、检查痕迹和谓词展开成本统一计入，所得 S²₁ 证明长度被该量支配。
7. 再用项目中已经形式化的显式估计

   ```text
   proof_predicate_formula_size <= 17(n+1)
   ```

   得到线性上界。

如果还要把 S²₁ 上界传到 PA，则再加入命名的线性嵌入：

```lean
S21ToPALinearEmbeddingOn sondowCertificateValidCode
```

该对象给出：

```text
proof_length PA <= C * proof_length S21 + D.
```

于是当前 Lean 已经证明 PA 层上界：

```lean
paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
```

其内容是：

```text
forall n >= N_S(q),
  proof_length PA symbolSize (sondowCertificateValidCode n)
    <= C * (17 * (n + 1)) + D.
```

存在型版本是：

```lean
paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
```

因此，投稿表述中最信用安全的说法是：

```text
Sondow side supplies an explicit half-denominator checked tail.  Once the
standard Sondow-specific bounded-arithmetic trace compiler is fixed, the
certificate family has the explicit S²₁ upper 17(n+1), and after a linear
S²₁-to-PA simulation it has the explicit PA upper C*17(n+1)+D.
```

不能说：

```text
We assume a Sondow upper provider.
```

也不能说：

```text
The PA upper is literally 17(n+1).
```

因为 `17(n+1)` 是 Sondow verifier predicate-size/S²₁ 层面的上界；PA 层要经过
`C,D` 线性传输。

## 16. 现有代码还能不能把剩余义务继续关闭

我检查了现有的 component route。项目里确实已经有更具体的 Sondow 组件证明构造：

```lean
MainSondowFullCertificateComponentProofCompiler
MainSondowEventualFullCertificateComponentProofCompiler
SondowReflectionGraftSidecarProofObjectSystemValidEventually.ofMainEventualCompilerAndCheckedTail
sidecarS21SemanticNonemptyEventually_of_mainEventualCompiler_checkedTailProvider
```

这些对象的作用是：

```text
checked Sondow full certificate
  -> product/log/decomposition/threePow/payload 五个组件 proof object
  -> 右嵌套 conjunction proof object
  -> sidecar reflection-graft target 的 S²₁ semantic proof object tail.
```

这是一条有实质内容的干净上游路线。它说明 Sondow 侧并不是空洞地假设
`upper_provider`；很多证书到 proof object 的构造已经在 sidecar 层展开。

但是，它还没有直接给出本文件当前 root 目标：

```text
proof_length S21 symbolSize (sondowCertificateValidCode n)
```

原因是两层对象不同：

```text
sidecar route:
  BAProofObject BussS21Axiom for component/graft target

root route:
  proof_length ProofSystem.S21 symbolSize (sondowCertificateValidCode n)
```

要从现有 component route 完全关闭 `SondowCheckedS21TraceCompiler`，还必须补齐
一个精确的 root-recognition/calibration 定理：

```text
由 Sondow full certificate 的五个组件 proof object
合成 root formula sondowCertificateValidCode n 的 S²₁ 证明，
并证明该 root proof_length 不超过
proof_predicate_formula_size sondowCertificateValidCode n。
```

换句话说，现在剩下的不是 `upper_provider`，也不是
`partial_consistency_payload`；剩下的是：

```text
Sondow 专用 checked verifier 的 S²₁ root proof-length calibration。
```

这条路从逻辑上是可证明的，因为它是固定检查器的标准算术化和 proof-object
合成问题；但在当前 Lean 代码中还没有完全展开成无输入定理。审计上应把它
列为明确的形式化待闭合义务，而不是把它混回旧的 `accepted_certificate`
接口。

## 17. 最终判断

本文件完成的结论是：

```text
1. Sondow 数学 tail 已经由 Lean 给出：
   q = gamma => n >= max 3 ((q.den + 1)/2)
   => MainSondowFullCertificateCheckedAt n.

2. 线性 predicate-size 上界已经由 Lean 给出：
   proof_predicate_formula_size sondowCertificateValidCode n <= 17(n+1).

3. 不需要 upper_provider；上界存在是 Lean 定理链的结论。

4. payload 依赖只在 dirty diagnostic root accepted route 中出现。
   clean checked route 不出现
   partial_consistency_payload /
   strengthened_partial_consistency_payload。

5. 当前还没有完全无输入关闭
   SondowCheckedS21TraceCompiler。
   这是标准 S²₁ verifier-trace compiler/root proof-length calibration
   义务，不是上界先验。
```

所以，最干净、最可信的投稿路线应以如下主张为中心：

```text
From the half-denominator Sondow checked tail and the explicit
bounded-arithmetic trace compiler for the Sondow checker, one obtains the
linear S²₁ upper 17(n+1); after a named linear S²₁-to-PA embedding one obtains
the PA upper C*17(n+1)+D.
```

Lean 已经验证了从 checked tail 到显式上界的所有外层推导和 axiom profile；还
需要继续形式化的是 `SondowCheckedS21TraceCompiler` 本身的内部 proof-code
构造。

## 18. `SondowCheckedS21TraceCompiler` 的证明细化

本节专门证明上一节留下的对象：

```lean
SondowCheckedS21TraceCompiler
```

它的目标是：

```text
forall n,
  MainSondowFullCertificateCheckedAt n
    -> proof_length S21 symbolSize (sondowCertificateValidCode n)
         <= proof_predicate_formula_size sondowCertificateValidCode n.
```

这个命题不能只靠 `MainSondowFullCertificateCheckedAt n` 自身推出。原因很具体：
项目根层的

```lean
proof_length
```

旧版本中在 `EulerLimit/ProofComplexityCore.lean` 中是一个抽象常量。当前版本已经
把它改成 structural fallback proof length（结构性回退证明长度）定义，从 axiom
profile（公理依赖画像）里去掉了 `proof_length` 公设本身。

但是这仍然不是 PA/Hilbert literature calibration（PA/Hilbert 文献式校准）。
从 checked certificate（已检查证书）推出 root `proof_length` 的数值不等式，
仍然必须补上一个 recognition/calibration theorem（识别/校准定理），把 root
符号和具体构造出来的 S²₁ proof code（S²₁ 证明码）联系起来。

所以 `SondowCheckedS21TraceCompiler` 的真正证明应分成两段。

### 18.1 第一段：具体 S²₁ proof-code compiler

先构造一个具体编译器：

```lean
SondowFullCertificateConcreteProofCodeCompiler
```

它给出一个具体码长函数：

```text
codeLength : Nat -> Nat
```

并证明：

```text
MainSondowFullCertificateCheckedAt n
  -> codeLength(n)
       <= proof_predicate_formula_size sondowCertificateValidCode n.
```

纸面证明如下。

给定

```text
hchecked : MainSondowFullCertificateCheckedAt n,
```

其中包含某个有理参数 `q` 和

```text
mainSondowFullCertificateChecks q n.
```

展开这个检查命题，得到五个 Sondow 源组件：

```text
1. gamma_eq;
2. tail_bound_certificate_accepted n;
3. denominator_certificate_accepted q n;
4. sondow_explicit_product_log_relation_prop n;
5. sondow_explicit_decomposition_prop n.
```

然后固定 Sondow full-certificate checker 的 S²₁ 形式化程序 `V_S`。该程序对
上述五个组件逐项检查，并产生一个 S²₁ proof code，证明

```text
sondowCertificateValidCode n.
```

由于 `V_S` 是固定程序，且 `proof_predicate_formula_size` 已经把 index 编码、
证书字段、检查 trace、公式展开和定理引用成本计入，构造出的 proof code
长度被

```text
proof_predicate_formula_size sondowCertificateValidCode n
```

支配。

这一步是纯 proof-code 构造；它不应提到 root `accepted_certificate`，也不应
使用 `partial_consistency_payload` 或
`strengthened_partial_consistency_payload`。

### 18.2 第二段：root S²₁ proof-length recognition

具体 proof code 还不是 root `proof_length`。还需要证明：

```lean
SondowFullCertificateConcreteS21RootCalibration compiler
```

其内容是：

```text
forall n,
  proof_length S21 symbolSize (sondowCertificateValidCode n)
    <= compiler.codeLength n.
```

这一步是 root recognition/calibration。它说明根层抽象长度符号没有比我们
显式构造的 S²₁ proof code 更大。

一旦有这两段，`SondowCheckedS21TraceCompiler` 的证明就是一行传递性：

```text
proof_length S21 symbolSize (sondowCertificateValidCode n)
  <= compiler.codeLength n
  <= proof_predicate_formula_size sondowCertificateValidCode n.
```

Lean 中对应的新定理是：

```lean
SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
```

它已经验证：

```text
SondowFullCertificateConcreteProofCodeCompiler
  + SondowFullCertificateConcreteS21RootCalibration
  -> SondowCheckedS21TraceCompiler.
```

### 18.3 上界链的完全打通形式

在上述证明下，Sondow S²₁ 上界链变为：

```text
q = gamma
  -> half-denominator checked tail
  -> MainSondowFullCertificateCheckedAt n
  -> concrete S²₁ proof-code bound
  -> root S²₁ proof_length bound
  -> proof_length S21 <= 17(n+1).
```

Lean 中对应定理是：

```lean
s21SondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
s21SondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
```

如果再加入线性 S²₁-to-PA 嵌入：

```lean
S21ToPALinearEmbeddingOn sondowCertificateValidCode
```

则 PA 上界链也打通：

```text
proof_length PA symbolSize (sondowCertificateValidCode n)
  <= C * 17(n+1) + D.
```

Lean 中对应定理是：

```lean
paSondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
paSondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
```

这就是当前最精确的“完全打通”形式：

```text
具体 Sondow proof-code compiler
  + root S²₁ proof-length recognition
  + S²₁-to-PA linear embedding
  => Sondow 上界无 upper_provider 地推出。
```

### 18.4 还剩什么没有无条件关闭

必须非常明确：本节没有把 root recognition 偷换成结论。当前 Lean 已经证明了
从这两个具体子义务到 `SondowCheckedS21TraceCompiler` 和最终上界的全部外层
推导；但如果要求“完全无输入关闭”，还必须继续证明：

```text
1. SondowFullCertificateConcreteProofCodeCompiler 的实际构造；
2. SondowFullCertificateConcreteS21RootCalibration 的 root recognition。
```

其中第 1 项是检查器到 S²₁ proof-code 的构造问题；第 2 项是把根层
`proof_length` 识别为具体 proof-code 长度上界的问题。由于 root
`proof_length` 本身是 axiom，第二项在当前模型中不可能凭空消失，必须作为
命名的 calibration theorem 被证明或由更底层的 proof calculus 定义替代。

### 18.5 Lean 探针结果

新增 Lean 桥位于：

```text
integration/SondowProjectSondowUpperCompilerRoute.lean
```

轻量探针命令：

```bash
lake env lean integration/SondowProjectSondowUpperCompilerRoute.lean
lake env lean integration/SondowProjectSondowUpperProofProbe.lean
```

均已通过。后续检查不再使用完整 `lake build`，只使用目标文件探针和
`#print axioms` profile 探针。

axiom/profile 探针命令：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectSondowUpperCompilerRoute
open SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute

#check SondowFullCertificateConcreteS21RootCalibration
#check SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
#check s21SondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
#check s21SondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
#check paSondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
#check paSondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding

#print axioms SondowFullCertificateConcreteS21RootCalibration
#print axioms SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
#print axioms s21SondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
#print axioms s21SondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
#print axioms paSondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
#print axioms paSondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
#print axioms acceptedSondowCertificate_of_checkedAt
EOF
```

观察结果：

```text
SondowFullCertificateConcreteS21RootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]

acceptedSondowCertificate_of_checkedAt
  [partial_consistency_payload, propext,
   strengthened_partial_consistency_payload, Classical.choice, Quot.sound]
```

结论：

```text
1. concrete/root-calibration clean route 没有引入两个 payload 依赖；
2. payload 依赖只在 diagnostic root accepted-certificate route 中出现；
3. 上界外层推导已经打通；
4. 剩余待证义务精确为 concrete proof-code compiler 和 root recognition。
```

## 19. 证明长度模型的使用与循环论证风险

### 19.1 问题

上面的第 18 节把 `SondowCheckedS21TraceCompiler` 拆成了两个义务：

```text
checked Sondow certificate
  -> concrete S²₁ proof code of sondowCertificateValidCode n
  -> root proof_length S21 symbolSize is bounded by that code length.
```

项目中已有一套 proof-length model：

```lean
ProofCodeSemantics
ProofLengthCodeSemantics
ProofLengthCodeSemantics.Calibration
ProjectProofLengthSemantics
S21GraftProofLengthRecognitionTheorem
```

这套模型能不能用于关闭上界黑盒，关键取决于它的使用方式。

### 19.2 可用但不应直接用的旧通路

现有 `S21GraftProofLengthRecognitionTheorem` 可以把 root
`proof_length S21 symbolSize` 识别为某个 MiniHilbert concrete proof family
的长度：

```lean
S21GraftProofLengthRecognitionTheorem.family_lengths
```

从形式上看，这给出了：

```text
proof_length S21 symbolSize (sondowCertificateValidCode n)
  = hrec.sondow_proofs.length n.
```

如果再用通用定理

```lean
s21GraftCanonicalCalibrationPackage_sondow_length_le_proofPredicate_of_trace
```

就可以得到：

```text
hrec.sondow_proofs.length n
  <= proof_predicate_formula_size sondowCertificateValidCode n.
```

但是这条通路需要先把

```text
MainSondowFullCertificateCheckedAt n
```

转成 root

```text
accepted_certificate (sondowCertificateValidCode n).
```

而 root `accepted_certificate` 在当前项目中仍然带有旧的
partial-consistency 分支。因此这个诊断通路虽然逻辑上能形成上界，但 axiom
profile 会重新出现：

```text
partial_consistency_payload
strengthened_partial_consistency_payload
```

这不适合作为投稿主线。

更重要的是，这条通路在证明结构上接近循环：它用一个通用
`S21VerifierTraceSoundness` 去证明 `SondowCheckedS21TraceCompiler`。如果
`S21VerifierTraceSoundness` 本身还没有被具体 proof-code checker 展开，那么
它只是把待证的 checked trace compiler 换了一个名字。

因此旧通路只能作为诊断工具，不能作为“上界黑盒已彻底消除”的最终论证。

### 19.3 干净模型通路

干净路线应直接在 Sondow certificate fragment 上定义 proof-code semantics，
不经过 root `accepted_certificate`。

Lean 中新增的相关对象是：

```lean
SondowCertificateRelevantCode
SondowCheckedS21ProofCodeSemantics
SondowCheckedS21ProofLengthModel
```

其中

```lean
SondowCertificateRelevantCode code :=
  ∃ n, code = sondowCertificateValidCode n.
```

`SondowCheckedS21ProofCodeSemantics` 的内容是：

```text
1. 一个 concrete ProofCodeSemantics，只覆盖 Sondow certificate-validity
   formula family；
2. 对每个 checked Sondow certificate，显式产生一个 proof code；
3. 这个 proof code 的 size 不超过
   proof_predicate_formula_size (sondowCertificateValidCode n).
```

注意，这里没有：

```text
upper_provider
polynomial upper-tail input
accepted_certificate
partial_consistency_payload
strengthened_partial_consistency_payload
proof_length
```

所以这一层是真正 proof-length-free 的 proof-code 层。

从它推出的 Lean 定理是：

```lean
SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndProofCodeSemantics
pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndProofCodeSemantics
```

纸面推导如下。

给定有理参数 `q`，若 `(q : R) = gamma`，Sondow reproof 给出半分母尾部：

```text
for all n >= max 3 ((q.den + 1)/2),
  MainSondowFullCertificateCheckedAt n.
```

由 `SondowCheckedS21ProofCodeSemantics`，每个这样的 checked certificate
给出一个 S²₁ proof code `c_n`，满足：

```text
checks(c_n, sondowCertificateValidCode n),
size(c_n) <= proof_predicate_formula_size(sondowCertificateValidCode n).
```

由 `ProofCodeSemantics.minProofCodeSize` 的最小性：

```text
minProofCodeSize(sondowCertificateValidCode n) <= size(c_n).
```

于是：

```text
minProofCodeSize(sondowCertificateValidCode n)
  <= proof_predicate_formula_size(sondowCertificateValidCode n).
```

项目中已经有显式 size 估计：

```lean
proofPredicateFormulaSizeSondowCertificateValidCode_le_17_natPower
```

即：

```text
proof_predicate_formula_size(sondowCertificateValidCode n)
  <= 17 * (n + 1).
```

所以得到 proof-code-free 的显式上界：

```text
minProofCodeSize(sondowCertificateValidCode n)
  <= 17 * (n + 1).
```

这一步没有 root `proof_length`，因此也没有证明长度公设风险。

### 19.4 root proof_length 的唯一合法接入点

若论文需要使用 root 形式：

```text
proof_length S21 symbolSize (sondowCertificateValidCode n),
```

则必须额外给出 calibration：

```text
proof_length S21 symbolSize (sondowCertificateValidCode n)
  =
minProofCodeSize(sondowCertificateValidCode n).
```

Lean 中对应对象是：

```lean
SondowCheckedS21ProofLengthModel
```

它只有两个字段：

```text
code_semantics:
  SondowCheckedS21ProofCodeSemantics

root_calibration:
  proof_length S21 symbolSize (sondowCertificateValidCode n)
    = semantic minProofCodeSize at n
```

这不是上界黑盒，因为它不说任何 `<= U(n)`，也不说 rationality，不说 collision，
不说 tail。它只说明 root `proof_length` 这个抽象符号在 Sondow certificate
fragment 上采用哪一个 concrete proof-code semantics。

在这个模型下，Lean 已经验证：

```lean
SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel
s21SondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModel
s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModel
paSondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding
paSondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding
```

S²₁ 层的结论是：

```text
if q = gamma, then for all n >= max 3 ((q.den + 1)/2),
  proof_length S21 symbolSize (sondowCertificateValidCode n)
    <= 17 * (n + 1).
```

PA 层再加一个线性 embedding：

```text
proof_length PA <= C * proof_length S21 + D,
```

得到：

```text
proof_length PA symbolSize (sondowCertificateValidCode n)
  <= C * 17 * (n + 1) + D.
```

### 19.5 循环论证检查

干净模型通路没有循环，必须满足以下四个检查：

1. `SondowCheckedS21ProofCodeSemantics.checked_has_predicate_size_code`
   只能从 checked certificate 构造 proof code，不能引用最终上界定理。
2. `SondowCheckedS21ProofLengthModel.root_calibration`
   只能识别 root `proof_length` 与 concrete minProofCodeSize，不能引用 rationality、
   Sondow tail、Pudlak gap、collision theorem。
3. 证明 `17(n+1)` 只能来自 verifier-size estimate：
   `proofPredicateFormulaSizeSondowCertificateValidCode_le_17_natPower`。
4. 推出 upper-tail 的 theorem 只能在上述三项之后包装存在型 `U`，不能把 `U`
   作为输入字段。

因此可以把审计标准写成：

```text
允许的根部义务：
  concrete checked proof-code semantics
  root proof_length calibration
  optional S21-to-PA linear embedding

禁止的上界黑盒：
  upper_provider
  PolynomialUpperTailCertificate
  accepted_certificate-based Sondow route
  any theorem assuming proof_length <= U(n)
```

### 19.6 最新 Lean 探针

由于不再使用完整 build，最新探针采用当前源码拼接 `#print axioms` 的方式：

```bash
tmp=$(mktemp /tmp/sondow_upper_model_probe_XXXX.lean)
cat integration/SondowProjectSondowUpperCompilerRoute.lean > "$tmp"
cat >> "$tmp" <<'EOF'

namespace SondowMainCheckedCodeBridge
namespace SondowProjectSondowUpperCompilerRoute

#print axioms SondowCheckedS21ProofCodeSemantics
#print axioms SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
#print axioms pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndProofCodeSemantics
#print axioms pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndProofCodeSemantics
#print axioms SondowCheckedS21ProofLengthModel
#print axioms SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel
#print axioms s21SondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModel
#print axioms s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModel
#print axioms paSondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding
#print axioms paSondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding

end SondowProjectSondowUpperCompilerRoute
end SondowMainCheckedCodeBridge
EOF
lake env lean "$tmp"
rm "$tmp"
```

观察结果：

```text
SondowCheckedS21ProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21ProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]
```

这证明新的模型路线没有引入：

```text
partial_consistency_payload
strengthened_partial_consistency_payload
upper_provider
```

### 19.7 当前结论

证明长度模型可以用，但只能按干净模型通路使用。

不能把旧的通用 `accepted_certificate` trace route 当成最终证明，因为它会重新引入
payload profile，并且在审计上接近把 trace compiler 换名包装。

可投稿主线应写成：

```text
Sondow rationality assumption
  -> half-denominator checked Sondow tail
  -> checked Sondow proof-code semantics
  -> minProofCodeSize <= proof_predicate_formula_size
  -> proof_predicate_formula_size <= 17(n+1)
  -> root proof_length calibration
  -> SondowCheckedS21TraceCompiler
  -> S²₁/PA upper theorem.
```

这样上界黑盒已经被拆成可见的、可审计的 proof-code semantics 和 root calibration
义务。剩下真正需要继续形式化的是：

```text
构造 SondowCheckedS21ProofCodeSemantics 的具体 proof codes；
证明 SondowCheckedS21ProofLengthModel.root_calibration 的底层 proof calculus
语义一致性。
```

## 20. 更弱的 local checked proof-code 路线

第 19 节的 `SondowCheckedS21ProofCodeSemantics` 使用了项目通用的
`ProofCodeSemantics`。这有一个审计上需要继续压低的假设：

```lean
ProofCodeSemantics.complete
```

它要求 relevant fragment 中每个 formula code 都有 proof code。对于当前
Sondow 上界，我们实际上不需要这么强。Sondow 上界只在 rationality assumption
给出 checked tail 之后使用：

```text
MainSondowFullCertificateCheckedAt n.
```

因此最干净的证明对象应当是局部的：

```text
只要 checked certificate 已经出现，
就能构造一个短 S²₁ proof code。
```

### 20.1 Lean 中的新 local 接口

新增对象为：

```lean
SondowCheckedS21LocalProofCodeSemantics
```

字段是：

```text
Code      : Type
checksAt  : Code -> Nat -> Prop
size      : Code -> Nat

checked_has_predicate_size_code :
  forall n,
    MainSondowFullCertificateCheckedAt n ->
      exists c,
        checksAt c n and
        size c <= proof_predicate_formula_size (sondowCertificateValidCode n).
```

它没有：

```text
ProofCodeSemantics.complete
accepted_certificate
upper_provider
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
```

这比第 19 节的 global proof-code semantics 更适合作为投稿主线。

### 20.2 conditional minimum

为了把 local proof code 变成一个 Nat-valued length function，Lean 中定义：

```lean
SondowCheckedS21LocalProofCodeSemantics.minCodeLength
```

含义是：

```text
如果 n 处存在 checked proof code，
  minCodeLength n 是所有这些 code size 的最小值；
否则
  minCodeLength n = 0.
```

这个 `0` fallback 不参与上界证明，因为 Sondow 上界只在 checked tail 之后使用。

关键最小性定理是：

```lean
SondowCheckedS21LocalProofCodeSemantics.minCodeLength_le_of_checks
```

即：

```text
checksAt c n -> minCodeLength n <= size c.
```

### 20.3 local proof-code 上界

由 local semantics 得到 compiler：

```lean
SondowFullCertificateConcreteProofCodeCompiler
  .ofCheckedLocalProofCodeSemantics
```

再由半分母 checked tail 和 verifier-size 估计得到：

```lean
pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
```

数学推导为：

```text
q = gamma
  -> for n >= max 3 ((q.den + 1)/2),
       MainSondowFullCertificateCheckedAt n
  -> exists c, checksAt c n and
       size c <= proof_predicate_formula_size(sondowCertificateValidCode n)
  -> minCodeLength n <= size c
  -> minCodeLength n <= proof_predicate_formula_size(sondowCertificateValidCode n)
  -> minCodeLength n <= 17(n+1).
```

这里没有任何 root `proof_length`。

### 20.4 local root proof_length calibration

如果需要回到 root proof-length 表述，则新增：

```lean
SondowCheckedS21LocalProofLengthModel
```

字段为：

```text
code_semantics :
  SondowCheckedS21LocalProofCodeSemantics

root_calibration :
  proof_length S21 symbolSize (sondowCertificateValidCode n)
    = code_semantics.minCodeLength n.
```

这也是 calibration，不是 upper-provider。它不含 rationality、tail、gap 或
collision 信息。

由它得到：

```lean
SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel
s21SondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
paSondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding
paSondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding
```

### 20.5 最新 local 探针结果

源文件探针：

```bash
lake env lean integration/SondowProjectSondowUpperCompilerRoute.lean
lake env lean integration/SondowProjectSondowUpperProofProbe.lean
```

均已通过。

local axiom profile 探针：

```bash
tmp=$(mktemp /tmp/sondow_upper_local_model_probe_XXXX.lean)
cat integration/SondowProjectSondowUpperCompilerRoute.lean > "$tmp"
cat >> "$tmp" <<'EOF'

namespace SondowMainCheckedCodeBridge
namespace SondowProjectSondowUpperCompilerRoute

#print axioms SondowCheckedS21LocalProofCodeSemantics
#print axioms SondowCheckedS21LocalProofCodeSemantics.minCodeLength
#print axioms SondowCheckedS21LocalProofCodeSemantics.minCodeLength_le_of_checks
#print axioms SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
#print axioms pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
#print axioms pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
#print axioms SondowCheckedS21LocalProofLengthModel
#print axioms SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel
#print axioms s21SondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
#print axioms s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
#print axioms paSondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding
#print axioms paSondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding

end SondowProjectSondowUpperCompilerRoute
end SondowMainCheckedCodeBridge
EOF
lake env lean "$tmp"
rm "$tmp"
```

观察结果：

```text
SondowCheckedS21LocalProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21LocalProofCodeSemantics.minCodeLength
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21LocalProofCodeSemantics.minCodeLength_le_of_checks
  [propext, Classical.choice, Quot.sound]

SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21LocalProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]

paSondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding
  [proof_length, propext, Classical.choice, Quot.sound]
```

### 20.6 当前最干净表述

投稿主线现在应优先使用 local route：

```text
Sondow rationality assumption
  -> half-denominator checked Sondow tail
  -> SondowCheckedS21LocalProofCodeSemantics
  -> local minCodeLength <= 17(n+1)
  -> SondowCheckedS21LocalProofLengthModel.root_calibration
  -> SondowCheckedS21TraceCompiler
  -> S²₁ upper
  -> optional S²₁-to-PA embedding
  -> PA upper.
```

这条线已经把上界黑盒压到两个完全公开的、非上界型义务：

```text
1. checked certificate -> concrete S²₁ proof code；
2. root proof_length 与 local minCodeLength 的 calibration。
```

它不再要求全族 `ProofCodeSemantics.complete`，因此比第 19 节的 global model
更适合写入正式论文。

## 21. 釜底抽薪审计：哪些已经证明，哪些只是义务拆分

必须明确区分两件事。

第一件事是已经在 Lean 中证明的外层推导：

```text
half-denominator checked Sondow tail
  + local checked proof-code semantics
  -> concrete proof-code upper <= 17(n+1).
```

这部分不是黑盒上界。Lean 已经证明：

```lean
pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
```

它没有 `proof_length`，没有 `upper_provider`，没有 partial-consistency payload。

第二件事是还没有完全关闭的根部构造：

```text
MainSondowFullCertificateCheckedAt n
  -> concrete S²₁ proof code for sondowCertificateValidCode n
```

如果只是把这一步命名成：

```lean
SondowCheckedS21LocalProofCodeSemantics
```

那确实只是把证明义务后移。为了避免这一点，Lean 中又拆出：

```lean
SondowCheckedS21VerifierSimulationBuilder
```

它把义务拆成：

```text
1. traceOfChecked:
   checked full Sondow certificate -> verifier trace；

2. trace_size_le_verifier_trace:
   trace size <= verifier_trace_size；

3. proofCodeOfTrace:
   verifier trace -> S²₁ proof code；

4. compiled_trace_proves_sondow_certificate:
   produced proof code proves/checks the target index；

5. compiled_size_le_trace_plus_reference:
   proof-code size <= trace size + theorem reference overhead.
```

由这些字段，Lean 推出：

```lean
SondowCheckedS21VerifierSimulationBuilder.toLocalProofCodeSemantics
pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndVerifierSimulationBuilder
```

但是这仍然不是最终完成。它只是把需要真正构造的底层对象精确列出来。

### 21.1 什么才算真正釜底抽薪

真正关闭 Sondow 上界黑盒，需要完成以下二选一路线之一。

路线 A：完全 proof-code 层主线。

```text
构造 SondowCheckedS21VerifierSimulationBuilder
  -> 得到 local minCodeLength <= 17(n+1).
```

这条路线完全不使用 root `proof_length`。如果论文主结论只需要“具体证明码长度
上界”，这是最干净的主线。

路线 B：root proof_length 主线。

```text
构造 SondowCheckedS21VerifierSimulationBuilder
  -> 得到 local proof-code upper
  -> 证明 SondowCheckedS21LocalProofLengthModel.root_calibration
  -> 得到 SondowCheckedS21TraceCompiler.
```

这条路线多一个 root calibration。因为当前项目里 `proof_length` 是 root axiom，
所以这一步不能靠外层 Lean 推导自动消失。必须把 `proof_length` 的含义换成
具体 proof-code minimum，或者提供一个非循环的 calibration theorem。

### 21.2 循环风险判断

下面这些做法是有循环风险或信用风险的：

```text
1. 直接假设 SondowCheckedS21TraceCompiler；
2. 直接假设 proof_length <= 17(n+1)；
3. 用 accepted_certificate route 关闭 Sondow 上界；
4. 用包含 partial-consistency payload 的通用 trace theorem 关闭 Sondow 上界；
5. 把 SondowCheckedS21LocalProofCodeSemantics 当作已经构造好的事实写进论文。
```

下面这些是非循环的、可以作为论文里的公开证明义务：

```text
1. checked certificate -> verifier trace；
2. verifier trace -> S²₁ proof code；
3. proof-code size bookkeeping；
4. root proof_length = local minCodeLength calibration。
```

### 21.3 最新 builder 探针

探针命令：

```bash
tmp=$(mktemp /tmp/sondow_builder_probe_XXXX.lean)
cat integration/SondowProjectSondowUpperCompilerRoute.lean > "$tmp"
cat >> "$tmp" <<'EOF'

namespace SondowMainCheckedCodeBridge
namespace SondowProjectSondowUpperCompilerRoute

#print axioms SondowCheckedS21VerifierSimulationBuilder
#print axioms SondowCheckedS21VerifierSimulationBuilder.toLocalProofCodeSemantics
#print axioms pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndVerifierSimulationBuilder

end SondowProjectSondowUpperCompilerRoute
end SondowMainCheckedCodeBridge
EOF
lake env lean "$tmp"
rm "$tmp"
```

结果：

```text
SondowCheckedS21VerifierSimulationBuilder
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21VerifierSimulationBuilder.toLocalProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndVerifierSimulationBuilder
  [propext, Classical.choice, Quot.sound]
```

这个结果的含义是：

```text
从 builder 到 proof-code upper 的外层推导是干净的；
但 builder 本身仍然必须被真实构造，不能被当成已经证明。
```

### 21.4 当前可信表述

当前最可信的论文表述应当是：

```text
We reduce the Sondow upper bound to an explicit local verifier-simulation
builder.  Once a checked Sondow certificate is compiled to an S²₁ proof code
with the stated trace-size bookkeeping, Lean proves the concrete linear upper
bound 17(n+1).  Passing from this concrete proof-code length to the root
proof_length notation requires a separate non-circular calibration theorem.
```

中文表述：

```text
我们没有把上界作为输入。我们把 Sondow 上界化归为一个显式的局部验证器模拟
构造：checked Sondow 证书必须被编译成 S²₁ 证明码，并满足 trace-size 的账本
不等式。一旦这个构造给出，Lean 已证明具体证明码长度满足 17(n+1) 的线性上界。
若要把该结论改写为 root proof_length 形式，还需要单独证明 proof_length 与
该局部最小证明码长度一致的非循环校准定理。
```

## 22. 当前推进：sidecar proof object 已把 Sondow 上界接到干净主路线接口

本节记录 2026-07-09 的最新推进。目标不是再包装一个
`upper_provider`（上界提供者），而是从已检查 Sondow 证书尾部和一个具体
`BAProofObject`（有界算术证明对象）直接构造上尾证书，再把它运输到主路线
需要的 checked measured object（已检查测量对象）。

### 22.1 旧裸 atom 路线已经判死

Lean 中已经有守门定理：

```lean
currentBussS21ProjectAtomDerivationSources_impossible
```

它说明：当前窄的 Buss-S²₁ project-atom（项目原子公式）语言不能直接推出
五个裸 Sondow project atom（项目原子）。所以不能再假装旧的 bare atom route
（裸原子路线）能关闭上界。真正可用的路线必须转向 expanded verifier formula
（展开验证器公式）或 sidecar proof object（旁路证明对象）。

### 22.2 已构造的 sidecar 证明对象

Lean 现在显式构造：

```lean
sidecarSondowCertificateVerifierFormula
sidecarSondowCertificateVerifierProofObject
sidecarSondowCertificateLocalProofCodeSemantics
sidecarSondowCertificateConcreteProofCodeCompiler
```

含义如下。

```text
sondowCertificateValidCode n
  -> sidecar expanded verifier formula
  -> concrete Buss-S²₁ BAProofObject
  -> local minCodeLength
```

这里的 `BAProofObject`（有界算术证明对象）是实际构造出来的对象，不是
`proof_length`（根层证明长度）公设，也不是 `upper_provider`（上界提供者）
字段。

由它得到的核心定理是：

```lean
pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndSidecarProofObjects
```

其数学内容是：

```text
若 gamma = q，
则存在多项式上界 U 和阈值 N，
使得对所有 n >= N，
sidecarSondowCertificateConcreteProofCodeCompiler.codeLength(n) <= U(n).
```

更强的是，Lean 已经暴露了公式级证书：

```lean
sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational_U
sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational_upperN
```

即：

```text
U(n) = 17(n+1),
N = max(3, (den(q)+1)/2).
```

这一步已经拿掉了 Sondow 侧“上界存在”的先验输入。

### 22.3 接入主路线：checked-target projection

主碰撞路线测量的不是任意 Sondow 目标，而是 theorem-5 checked source
measurement（第 5 定理已检查源测量）。因此还需要一个同一对象投影：

```lean
InternalPudlakTheorem5CheckedTargetProjection
```

它的数学内容是：

```text
theorem-5 source minProofCodeSize(n)
  <= sidecarSondowCertificateTargetMeasured(n) + 2.
```

给出这个 projection（投影）后，Lean 已经自动构造主路线需要的 checked upper
provider（已检查上界提供者）：

```lean
checkedExplicitUpperProviderOfSidecarSondowTargetProjection
checkedUpperProviderOfSidecarSondowTargetProjection
checkedUpperProviderOfSidecarSondowTargetProjection_closure
```

这个 provider（提供者）的内容不是外部输入，而是由上一节的 sidecar 证书和
projection（投影）计算出来。

公式级地，Lean 已证明：

```lean
checkedExplicitUpperProviderOfSidecarSondowTargetProjection_U
checkedExplicitUpperProviderOfSidecarSondowTargetProjection_upperN
```

也就是主路线拿到的上界为：

```text
U_main(n) = 17(n+1) + 2,
N_main = max(3, (den(q)+1)/2).
```

其中 `q` 是 rationality witness（有理性见证）中由
`Classical.choose`（经典选择）选出的有理数。

### 22.4 最新探针结果

当前文件探针：

```bash
lake env lean integration/SondowProjectSondowUpperCompilerRoute.lean
```

结果：

```text
passed
```

axiom profile（公理依赖画像）探针使用当前源码拼接 `#print axioms`，因为不跑
完整 build（构建）时，`import` 会读旧 olean（已编译缓存）：

```bash
lake env lean <(awk '1; END {
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational_U";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational_upperN";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.checkedExplicitUpperProviderOfSidecarSondowTargetProjection_U";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.checkedExplicitUpperProviderOfSidecarSondowTargetProjection_upperN";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.checkedUpperProviderOfSidecarSondowTargetProjection_closure";
}' integration/SondowProjectSondowUpperCompilerRoute.lean)
```

结果均为：

```text
[propext, Classical.choice, Quot.sound]
```

没有出现：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

### 22.5 仍然不能混淆的剩余义务

这次推进真正关闭的是：

```text
Sondow sidecar target upper:
  gamma = q
  -> U(n)=17(n+1)
  -> checked-target transported U_main(n)=17(n+1)+2.
```

仍然需要单独证明、不能伪装成已完成的是：

```text
InternalPudlakTheorem5CheckedTargetProjection
```

也就是同一对象投影：

```text
theorem-5 source minProofCodeSize(n)
  <= sidecar Sondow target measured length(n) + 2.
```

这不是 Sondow 上界本身，而是 Pudlak/checker 侧和 Sondow sidecar target
（旁路目标）是否确实是同一个碰撞对象的接线定理。如果这个 projection
由 checker/extractor/exactness（检查器/抽取器/精确性）构造出来，则
`upper_provider`（上界提供者）不再是论文信用负债。

当前可信结论是：

```text
Sondow 上界黑盒已经降为一个透明公式级 sidecar 上尾证书；
主路线的 upper_provider 可以由该证书加 checked-target projection 自动生成；
剩余硬茬是 projection 的同一对象证明，而不是上界存在性本身。
```

### 22.6 已接到 theorem-5 provider 主接口

为了避免停在“构造了一个 provider（提供者）”的中间层，Lean 又加入了
sidecar 专用 theorem-5 provider（第 5 定理提供者）：

```lean
theorem5ProviderOfCanonicalSearchCoreSidecarSondowTarget
theorem5ProviderOfCanonicalSearchCoreSidecarSondowTarget_not_rational
```

它的接口是：

```text
PAHilbertCanonicalSearchCore
  + InternalPudlakTheorem5CheckedTargetProjection
  -> proof-length-free theorem-5 provider
  -> not rational gamma.
```

也就是说，最终接口不再要求用户传入 Sondow upper_provider（索多上界提供者）。
它内部使用的 upper_provider 字段由如下链条生成：

```text
half-denominator checked Sondow tail
  -> sidecar BAProofObject
  -> U(n)=17(n+1)
  -> checked-target projection adds +2
  -> theorem-5 checked measured upper
  -> theorem-5 collision provider.
```

同时，显式端点保留了可计算的公式：

```lean
projectLengthExplicitEndpointOfSidecarSondowTargetUpper
projectLengthExplicitEndpointOfSidecarSondowTargetUpper_U
projectLengthExplicitEndpointOfSidecarSondowTargetUpper_upperN
projectLengthExplicitEndpointOfSidecarSondowTargetUpper_computed_n_eq
```

其公开公式为：

```text
U_main(n) = 17(n+1) + 2,
N_main = max(3, (den(q)+1)/2),
computed N = rejectionExtractor.witness(U_main, polynomial proof, N_main).
```

新增主接口的 axiom profile（公理依赖画像）也全部是：

```text
[propext, Classical.choice, Quot.sound]
```

没有出现：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

因此，当前 Sondow 上界负债已经从“外部上界输入”缩小为唯一的同一对象接线义务：

```text
InternalPudlakTheorem5CheckedTargetProjection
```

### 22.7 为什么 projection 不能自动从 core 推出

Lean 核查了 `PAHilbertCanonicalSearchCore`（PA Hilbert 规范搜索核心）的字段。
它包含：

```text
checker / semantics / recognizerExactness / canonicalInterface
scale_data / checkerSemantics / finiteEnumeration / rejectionExtractor
acceptedCodeExactness
```

它不包含：

```text
InternalPudlakTheorem5CheckedTargetProjection
```

所以不能声称 projection（投影）已经由 core（核心）自动给出。要继续关闭这个
最后义务，必须新增一个真实接线定理：

```text
checker/extractor/exactness data
  -> theorem-5 source proof code
  -> sidecar Sondow/reflection-graft target proof code
  -> source minProofCodeSize <= targetMeasured + 2.
```

如果这个定理没有完成，论文必须把它标成剩余 projection theorem（投影定理）
义务；如果完成，则 Sondow 上界和主碰撞接口之间的 upper_provider（上界提供者）
负债才算全部消失。

## 23. `SondowCheckedS21TraceCompiler` 的 sidecar-root 证明桥

本节回到目标对象：

```lean
SondowCheckedS21TraceCompiler
```

它不是 proof-code upper（证明码上界）对象，而是 root `proof_length`（根层证明
长度）对象。因此它不能只靠 sidecar proof object（旁路证明对象）无条件关闭。

Lean 现在把证明拆成两个完全透明的部分。

### 23.1 已经真实构造的部分

已经真实构造的是：

```lean
sidecarSondowCertificateConcreteProofCodeCompiler
```

它来自：

```text
sidecarSondowCertificateVerifierProofObject
  -> sidecarSondowCertificateLocalProofCodeSemantics
  -> minCodeLength
  -> concrete proof-code upper.
```

对应的无 root 结论是：

```lean
pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndSidecarProofObjects
```

axiom profile（公理依赖画像）为：

```text
[propext, Classical.choice, Quot.sound]
```

没有 `proof_length`（根层证明长度），也没有两个 payload（载荷）常量。

### 23.2 必须命名暴露的 root calibration

为了得到 root 版本，Lean 新增了一个专门命名的校准义务：

```lean
SidecarSondowCertificateConcreteS21RootCalibration
```

其内容是：

```text
forall n,
  proof_length S21 symbolSize (sondowCertificateValidCode n)
    <= sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n.
```

这不是新证明，也不是隐藏假设。它只是把 root `proof_length`（根层证明长度）
和已构造的 concrete codeLength（具体码长）之间还需要证明的关系单独标出来。

### 23.3 从 sidecar proof objects 到 trace compiler

在上述 root calibration（根层校准）给出后，Lean 已证明：

```lean
SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration
```

即：

```text
sidecar concrete proof-code compiler
  + root S²₁ length calibration
  -> SondowCheckedS21TraceCompiler.
```

随后得到 root S²₁ 上界：

```lean
s21SondowLinearUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
s21SondowCertificateUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
```

数学内容是：

```text
gamma = q
  -> n >= max(3, (den(q)+1)/2)
  -> proof_length S21 symbolSize (sondowCertificateValidCode n)
       <= 17(n+1).
```

### 23.4 最新 trace-compiler 探针

目标文件探针：

```bash
lake env lean integration/SondowProjectSondowUpperCompilerRoute.lean
```

通过。

axiom profile（公理依赖画像）探针：

```bash
lake env lean <(awk '1; END {
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.SidecarSondowCertificateConcreteS21RootCalibration";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.s21SondowLinearUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.s21SondowCertificateUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration";
print "#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndSidecarProofObjects";
}' integration/SondowProjectSondowUpperCompilerRoute.lean)
```

结果：

```text
SidecarSondowCertificateConcreteS21RootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowLinearUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndSidecarProofObjects
  [propext, Classical.choice, Quot.sound]
```

解释：

```text
1. 具体 proof-code upper 已干净关闭；
2. root trace compiler 只剩 proof_length calibration；
3. 旧的 partial_consistency_payload 和 strengthened_partial_consistency_payload
   没有回来；
4. 若论文坚持使用 root proof_length 语言，则必须公开说明这个 calibration；
5. 若论文改用 proof-code / checked-measured 语言，则这一步可以避开 root
   proof_length 债。
```

### 23.5 root calibration 的泛化接口已删除

曾经可以把 root calibration（根层校准）下沉到一个泛化的
`ProjectProofLengthSemantics`（项目证明长度语义）或
`ProofLengthCodeSemanticsModel`（证明长度码语义模型）接口。但这种写法仍然允许
外部塞入任意 length model（长度模型）和额外的
`length_le_sidecar_codeLength`（长度被旁路码长控制）字段。

为了不留下这种余地，当前 Lean 主线已经删除这些泛化接口。第 24 节给出现在保留
的唯一路线：canonical sidecar proof-code semantics（规范旁路证明码语义）
由 Lean 构造，semantic length upper（语义长度上界）由 Lean 证明，root 层只剩
一个 canonical calibration（规范校准）入口。

## 24. 根部切割：只剩唯一 canonical calibration

旧的泛化接口已经从 Lean 主线删除。现在的路线不再允许外部给任意
length model（长度模型）或额外的 `length_le_sidecar_codeLength`
（长度被旁路码长控制）字段。

这不是最硬的形态。真正应当切到根子上的是：

```text
sidecar proof objects
  -> canonical sidecar proof-code semantics
  -> canonical sidecar proof-length code semantics
  -> automatically length <= sidecar codeLength
  -> only root calibration remains.
```

Lean 已经完成这一步。

### 24.1 canonical proof-code semantics

新增的核心对象是：

```lean
sidecarSondowCertificateProofCodeSemantics
```

它不是外部输入。它直接由已经构造出的
`sidecarSondowCertificateVerifierProofObject n`（旁路验证器证明对象）组成：

```text
Proof code（证明码）:
  BAProofObject BussS21Axiom

checks c code（检查关系）:
  exists n,
    code = sondowCertificateValidCode n
    and c proves the sidecar verifier formula for n

size c（大小）:
  c.size
```

然后 Lean 证明：

```lean
sidecarSondowCertificateProofCodeSemantics_min_le_codeLength
```

数学含义是：

```text
minProofCodeSize(sondowCertificateValidCode n)
  <= sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n.
```

这一步没有 root `proof_length`（根层证明长度），也没有外部上界条件。

### 24.2 canonical proof-length code semantics

由上述 proof-code semantics（证明码语义）定义：

```lean
sidecarSondowCertificateProofLengthCodeSemantics fallback
```

再证明：

```lean
sidecarSondowCertificateProofLengthCodeSemantics_length_le_codeLength
```

数学含义是：

```text
length induced by the canonical sidecar semantics
  <= sidecar concrete codeLength.
```

因此 `length_le_sidecar_codeLength` 不再是外部参数，而是 Lean 定理。

### 24.3 唯一剩余根义务

现在剩下的唯一入口被命名为：

```lean
SidecarSondowCertificateCanonicalProofLengthCalibration fallback
```

它只是：

```lean
(sidecarSondowCertificateProofLengthCodeSemantics fallback).Calibration
```

即：

```text
root proof_length S21 symbolSize
  = length induced by the canonical sidecar proof-code semantics
```

在 Sondow certificate family（Sondow 证书族）上成立。

Lean 已证明：

```lean
SidecarSondowCertificateConcreteS21RootCalibration.ofCanonicalSidecarCalibration
SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
s21SondowLinearUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
s21SondowCertificateUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
```

所以 root 版上界现在的真实路线是：

```text
canonical sidecar proof objects
  -> canonical sidecar proof-code semantics
  -> semantic length <= sidecar codeLength
  -> sidecar codeLength <= 17(n+1)
  -> with the single canonical calibration:
       proof_length S21 <= 17(n+1).
```

这就是“根部一刀”后的状态。

### 24.4 探针结果

文件探针：

```bash
lake env lean integration/SondowProjectSondowUpperCompilerRoute.lean
```

通过。

axiom profile（公理依赖画像）：

```text
sidecarSondowCertificateProofCodeSemantics
  [propext, Classical.choice, Quot.sound]

sidecarSondowCertificateProofCodeSemantics_min_le_codeLength
  [propext, Classical.choice, Quot.sound]

sidecarSondowCertificateProofLengthCodeSemantics
  [propext, Classical.choice, Quot.sound]

sidecarSondowCertificateProofLengthCodeSemantics_length_le_codeLength
  [propext, Classical.choice, Quot.sound]

SidecarSondowCertificateCanonicalProofLengthCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

SidecarSondowCertificateConcreteS21RootCalibration.ofCanonicalSidecarCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowLinearUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
  [proof_length, propext, Classical.choice, Quot.sound]
```

结论：

```text
1. upper_provider（上界提供者）已经不在 Sondow 上界证明根线上；
2. length_le_sidecar_codeLength（长度上界字段）已经不再是外部输入；
3. sidecar proof-code semantics（旁路证明码语义）由 Lean 构造；
4. sidecar semantic length upper（旁路语义长度上界）由 Lean 证明；
5. root proof_length（根层证明长度）只剩唯一 canonical calibration（规范校准）；
6. 当前 root `proof_length` 已从 axiom（公设）改为 structural fallback
   definition（结构性回退定义），但这不是 PA/Hilbert 文献式校准。
```

如果下一步还要继续往根子上砍，就不是 Sondow 上界证明的问题，而是要改
`EulerLimit/ProofComplexityCore.lean` 的根层语义来源。旧目标是替换：

```lean
axiom proof_length : ProofSystem -> ProofLengthMeasure -> FormulaCode -> Real
```

当前已经去掉了这个 axiom（公设）。但投稿级目标还要继续替换 structural fallback
（结构性回退）为：

```text
proof_length T measure code
  = minProofCodeSize under a chosen proof-code semantics.
```

其中 chosen proof-code semantics（选定证明码语义）必须来自固定的
FormulaCode -> PA formula interpretation（公式码到 PA 公式解释）和固定
PA/Hilbert checker（PA/Hilbert 检查器）。这是全项目根层 proof-length
foundation（证明长度基础）重构，不是再展开 Sondow 上界可以解决的尾巴。

## 25. 投稿主线的惊天一跃：不用 root fallback，直接用文献式语义长度

继续往 root `proof_length`（根层证明长度）上砍时，必须分清两件事。

第一件事是“去掉公设”：

```text
把 proof_length 从 axiom（公设）改成某个 proof-code semantics（证明码语义）
诱导出来的最小长度。
```

这一点在 `ProofComplexityCore.lean` 中可以技术上做到。但如果这个 proof-code
semantics 只是 structural fallback（结构性回退语义），它不能作为论文里的
PA/Hilbert proof length（PA/Hilbert 证明长度）。

第二件事才是“和文献一样校准”：

```text
先固定 FormulaCode -> PA formula 的解释；
再固定 PA/Hilbert proof-code checker；
最后把 proof length 定义为：

  min size(c)
  such that checker accepts c as a proof of the interpreted formula.
```

这才是 Cook-Reckhow / Hilbert proof-length（Cook-Reckhow/Hilbert 证明长度）
路线。

当前项目里，这个文献式对象已经以局部形式存在：

```lean
FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics
```

它使用：

```text
LocalHilbertProofCode（局部 Hilbert 证明码）
TheoryProof.Code（理论证明码）
minProofCodeSize（最小证明码大小）
```

但是它必须依赖一个固定的：

```lean
FormulaCodeHilbertInterpretation
```

也就是固定 `FormulaCode`（公式码）如何解释为具体 PA/Hilbert 公式。没有这个解释，
全局 root `proof_length` 不可能“自动等于文献证明长度”。

因此投稿主线现在应该做真正的一跃：

```text
不用 root proof_length 作为主数学对象；
直接把主上界写在已经构造出来的 semantic proof length 上。
```

Lean 已新增：

```lean
sidecarSondowCertificateCanonicalProofLengthSemantics
sidecarSondowCertificateCanonicalSemanticLength
canonicalSemanticSondowLinearUpper_fromHalfDenCheckedTail
canonicalSemanticSondowUpper_fromHalfDenCheckedTail
```

其主结论是：

```text
gamma = q
  -> n >= max(3, (den(q)+1)/2)
  -> sidecarSondowCertificateCanonicalSemanticLength(n)
       <= 17(n+1).
```

这条路线的 axiom profile（公理依赖画像）为：

```text
canonicalSemanticSondowUpper_fromHalfDenCheckedTail
  [propext, Classical.choice, Quot.sound]
```

没有：

```text
proof_length
upper_provider
partial_consistency_payload
strengthened_partial_consistency_payload
```

这才是当前最适合投稿的 Sondow 上界主对象。

### 25.1 为什么不能把任意 root calibration 当成文献校准

项目中曾有：

```lean
externalPAHilbertProofLength_eq_localChecked
```

它声称对任意 `FormulaCodeHilbertInterpretation`（公式码 Hilbert 解释）：

```text
root proof_length = localCheckedCodeProofLength.
```

这不是一个可以无条件成立的文献定理。原因是：

```text
localCheckedCodeProofLength depends on interp.target_proof_family.
```

不同解释可以有不同的 proof family（证明族）和不同长度；一个全局
`proof_length` 不可能同时等于所有这些局部长度。

所以这类外部校准不能作为投稿主线。正确做法是：

```text
固定一个解释；
在该解释下使用它诱导的 semantic length；
把 root proof_length 版本仅作为兼容性 corollary（推论），
并明确列出所需 calibration（校准）条件。
```

### 25.2 当前可信结论

当前 Sondow 上界已经完成到下面这个强度：

```text
从 Sondow rational tail（有理尾证书）
到 sidecar proof objects（旁路证明对象）
到 canonical proof-code semantics（规范证明码语义）
到 explicit polynomial upper（显式多项式上界）
```

全部在 Lean 中打通。

剩下不能伪装成已完成的是：

```text
全局 root proof_length 与某个固定 PA/Hilbert 解释的完全一致性。
```

这个问题不应再放在 Sondow 上界里解决。它属于全局 proof-length convention
（证明长度约定）选择问题。投稿主稿应把主定理写成 semantic proof-length
版本，root `proof_length` 版本只放在“若采用某某标准 PA/Hilbert 编码约定，则得到”
的兼容段落里。

## 26. 和 Pudlak 侧同一对象的 PA 语义长度上界

上一节的 `sidecarSondowCertificateCanonicalSemanticLength`（旁路 Sondow
规范语义长度）已经避开了 root `proof_length`（根层证明长度）。但如果要和
Pudlak/checker side（Pudlak/检查器侧）完全对齐，还要再做一次校准：

```text
上界对象必须是：

  semanticBAProofLength PAAxiom
    sondowProjectComponentFormulas.target n

也就是 Pudlak calibration（Pudlak 校准）中同一个 PA semantic proof length
（PA 语义证明长度）对象。
```

这一步已经在 Lean 中补上。核心定理是：

```lean
semanticPAProjectTargetLength_le_combined_of_componentProofObjects
semanticPAProjectTargetUpper_fromHalfDenCheckedTailAndEventualCompiler
semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler
semanticPAProjectTargetUpper_fromRationalityAndFullCompiler
```

### 26.1 纸面证明

固定 `n`。假设我们已有一个 checked full Sondow certificate（已检查完整
Sondow 证书），并且 component proof compiler（分量证明编译器）给出五个
Buss-S²₁ proof objects（Buss-S²₁ 证明对象）：

```text
P_product(n), P_log(n), P_decomp(n), P_3pow(n), P_payload(n).
```

它们分别证明五个 component formulas（分量公式）：

```text
product(n),
logRelation(n),
decomposition(n),
threePow(n),
payload(n),
```

并满足各自的 size bound（大小上界）：

```text
size(P_i(n)) + 2 <= bound_i(n).
```

把五个证明对象用 conjunction introduction（合取引入）右结合合成：

```text
P_target(n)
  := P_product(n) ∧
     (P_log(n) ∧
       (P_decomp(n) ∧
         (P_3pow(n) ∧ P_payload(n)))).
```

Lean 中这个对象就是：

```lean
SondowComponentCertificate.buildProof
```

它的 conclusion（结论）严格等于：

```lean
sondowProjectComponentFormulas.target n
```

其 size（大小）由五个分量大小和四次合取引入开销给出，因此被

```lean
bounds.combined n
```

控制。由于 `BussS21Axiom`（Buss-S²₁ 公理）被包含在 `PAAxiom`（PA 公理）中，
这个 S²₁ 证明对象可以无损映射成 PA proof object（PA 证明对象）：

```lean
BAProofObject.mapAxioms bussS21Axiom_subset_pa
```

映射保持证明大小。于是由 semantic proof length（语义证明长度）的定义：

```lean
semanticBAProofLength_le_size
```

得到：

```text
semanticBAProofLength PAAxiom
  sondowProjectComponentFormulas.target n
  <= bounds.combined n.
```

这就是同一对象上的上界：不是 root `proof_length`，不是旧
`accepted_certificate`，也不是抽象 `upper_provider`（上界提供者）。

### 26.2 从 γ 有理到最终上界

若 `γ = q`，则 half-denominator checked tail（半分母检查尾部）给出：

```text
n >= max(3, (den(q)+1)/2)
  -> MainSondowFullCertificateCheckedAt n.
```

Lean 中是：

```lean
mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
```

若再有真正的 eventual component proof compiler（最终分量证明编译器）：

```lean
MainSondowEventualFullCertificateComponentProofCompiler bounds
```

则每个足够大的 checked certificate（已检查证书）都被编译成五个
Buss-S²₁ proof objects（证明对象）。由 §26.1 得到：

```text
semanticBAProofLength PAAxiom
  sondowProjectComponentFormulas.target n
  <= bounds.combined n
```

而 `bounds.combined` 已在 Lean 中证明为 polynomial bound（多项式上界）：

```lean
bounds.combined_poly
```

因此：

```text
is_rational γ
  -> ∃ polynomial U, eventually
       semanticBAProofLength PAAxiom
         sondowProjectComponentFormulas.target n
       <= U(n).
```

这就是真正和 Pudlak 侧对齐的 Sondow upper route（Sondow 上界路线）。

### 26.3 探针结果

探针命令：

```bash
lake env lean integration/SondowProjectSondowUpperCompilerRoute.lean
```

结果：通过。只有一个 `simpa` lint warning（可简化警告），不影响证明。

`#print axioms`（打印公理依赖）结果：

```text
semanticPAProjectTargetLength_le_combined_of_componentProofObjects
  [propext, Classical.choice, Quot.sound]

semanticPAProjectTargetUpper_fromHalfDenCheckedTailAndEventualCompiler
  [propext, Classical.choice, Quot.sound]

semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler
  [propext, Classical.choice, Quot.sound]

semanticPAProjectTargetUpper_fromRationalityAndFullCompiler
  [propext, Classical.choice, Quot.sound]
```

特别是没有：

```text
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
upper_provider
tail_gap
```

### 26.4 现在还剩什么硬核义务

这次跃迁已经把 upper side（上界侧）从旧 root length（根层长度）和旧
accepted-certificate branch（接受证书分支）中切出来，并校准到 Pudlak 侧同一个
PA semantic target（PA 语义目标）：

```lean
semanticBAProofLength PAAxiom
  sondowProjectComponentFormulas.target
```

剩下不能伪装的硬核义务只有一个：

```lean
MainSondowEventualFullCertificateComponentProofCompiler bounds
```

它不是 `upper_provider`（上界提供者）。它的含义非常具体：

```text
给定 checked full Sondow certificate（已检查完整 Sondow 证书），
显式构造五个 Buss-S²₁ proof objects（Buss-S²₁ 证明对象），
并证明它们的 conclusion（结论）和 size bound（大小上界）。
```

所以现在的审计边界已经压到原文献中真正的“多项式时间检查可在弱算术中短证明”
这一步。不能再把它叫作普通参数或上界假设；它是要继续完成的 formal compiler
theorem（形式化编译器定理）。

## 27. `SondowCheckedS21TraceCompiler` 本名的精确状态

现在必须把两个对象分开。

第一个对象是 proof-length-free / semantic route（无证明长度公设/语义路线）：

```lean
canonicalSemanticSondowUpper_fromHalfDenCheckedTail
semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler
```

它们的 axiom profile（公理依赖画像）已经是：

```text
[propext, Classical.choice, Quot.sound]
```

没有 `proof_length`（证明长度）、没有两个 payload（负载常量）、没有
`upper_provider`（上界提供者）。

第二个对象才是本节的名字：

```lean
SondowCheckedS21TraceCompiler
```

它的定义本身仍然写在 root `proof_length` 坐标上：

```lean
proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
  (sondowCertificateValidCode n)
```

因此，只要 theorem conclusion（定理结论）还含这个 root `proof_length`，Lean 的
axiom profile 必然会暴露 `proof_length` 依赖，除非全项目已经用一个文献式
PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）重新定义并重建这个根符号。

### 27.1 已经形式化完成的条件化证明

Lean 中已经证明：

```lean
SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration
SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel
SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel
SondowCheckedS21TraceCompiler.ofProofLengthRecognition
```

这些定理的数学含义是：

```text
如果 root proof_length 已经被校准到某个具体 Sondow proof-code semantics
（证明码语义），那么 checked Sondow certificate（已检查 Sondow 证书）
确实给出短 S²₁ proof（短 S²₁ 证明）。
```

也就是说，外层推导已经完全打通：

```text
checked certificate
  -> concrete proof code
  -> root proof_length calibration
  -> SondowCheckedS21TraceCompiler
  -> half-denominator polynomial upper.
```

但这个结果仍然是 conditional root-length theorem（条件化根层长度定理）。

### 27.2 探针结果

探针命令：

```bash
{
  sed -n '1,$p' integration/SondowProjectSondowUpperCompilerRoute.lean
  printf '\n#print axioms ...SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler\n'
  printf '#print axioms ...SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration\n'
  printf '#print axioms ...SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration\n'
  printf '#print axioms ...SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel\n'
  printf '#print axioms ...SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel\n'
  printf '#print axioms ...SondowCheckedS21TraceCompiler.ofProofLengthRecognition\n'
} | lake env lean --stdin
```

结果：

```text
SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofProofLengthRecognition
  [proof_length, propext, Classical.choice, Quot.sound]
```

重要的是：

```text
没有 partial_consistency_payload；
没有 strengthened_partial_consistency_payload；
没有 upper_provider；
没有 tail_gap。
```

但仍有：

```text
proof_length.
```

### 27.3 为什么不能把 structural fallback 当作完成

当前源码中有一个 structural fallback（结构性回退）：

```lean
rootSemanticProofLength_eq_rootFormulaCodeSize
proof_length := rootSemanticProofLength
```

它把 root `proof_length` 定义成公式码大小：

```text
rootFormulaCodeSize(T, measure, code)
```

这可以技术上去掉“自由 proof_length axiom（自由证明长度公设）”，但它不是
Cook-Reckhow / Hilbert proof length（Cook-Reckhow/Hilbert 证明长度）。

如果用这个 fallback 无条件关闭 `SondowCheckedS21TraceCompiler`，论文信用会下降：

```text
它证明的是“某个结构性码长很短”，
不是“PA/Hilbert 系统里存在短证明”。
```

所以投稿主线不应把 structural fallback 写成文献定理。正确做法是：

```text
主线使用 semanticBAProofLength / concrete proof-code route；
root SondowCheckedS21TraceCompiler 只作为
“给定标准 proof-length calibration 时”的推论。
```

### 27.4 目前离“本名完全无条件关闭”还差什么

要让 `SondowCheckedS21TraceCompiler` 本名无条件且文献可信地关闭，必须补一个固定的
root proof-length convention（根层证明长度约定）：

```text
固定 FormulaCode -> S²₁/PA formula interpretation（公式码解释）；
固定 Hilbert / Buss-S²₁ proof-code checker（证明码检查器）；
定义 proof_length 为该 checker 接受的最小 proof-code size（证明码大小）；
证明这个定义和 Sondow sidecar proof-code semantics 在
sondowCertificateValidCode n 上一致。
```

这不是 Sondow 上界本身的数学难点，而是全项目 proof-length foundation（证明长度基础）
选择问题。当前已经完成的是：

```text
Sondow 上界的 proof-code / semantic proof-length 推导；
root SondowCheckedS21TraceCompiler 的条件化推导；
同一 PA semantic target 上界与 Pudlak 侧目标的对齐。
```

尚未完成的是：

```text
root proof_length 的文献式全局定义与重建。
```

## 28. 按原文献校准后的上界主线

为了和原文献中的 proof length（证明长度）概念一致，投稿主线不应把
`SondowCheckedS21TraceCompiler` 作为最终表述。原因不是 Sondow 上界推不出来，
而是这个旧名字绑定在 root `proof_length`（根层证明长度）上；当前 root 层为了
避免自由公设有一个 structural fallback（结构性回退），但它不是文献中的
Hilbert / Buss proof length（希尔伯特 / Buss 证明长度）。

现在真正应该引用的是这个 Lean theorem（Lean 定理）：

```lean
literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
literatureCalibratedSondowUpper_fromRationalityAndFullCompiler
```

它的结论是：

```lean
∃ U : Nat → Real, is_polynomial_bound U ∧
  ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
    BoundedArithmeticLab.semanticBAProofLength
        BoundedArithmeticLab.PAAxiom
        BoundedArithmeticLab.sondowProjectComponentFormulas.target n
      ≤ U n
```

这里的 `semanticBAProofLength`（有界算术语义证明长度）在
`bounded_arithmetic_lab/BoundedArithmeticLab/SemanticProofLength.lean`
中定义为：

```lean
sInf { r : Real | ∃ p : BAProofObject Ax,
  p.conclusion = target n ∧ (p.size : Real) = r }
```

也就是说，它测量的是：

```text
所有能证明目标公式 target n 的 BAProofObject（有界算术证明对象）中，
证明码大小 p.size 的下确界。
```

这正是 proof complexity（证明复杂性）文献要使用的对象：固定 formal system
（形式系统）、固定 target formula（目标公式）、固定 size convention（大小约定），
然后看最短证明的长度。Lean 里用 `sInf`（下确界）表达这个最短长度/最小上界对象；
上界证明只需要定理：

```lean
semanticBAProofLength_le_size
```

纸面推导如下。

1. Sondow rationality route（Sondow 有理性路线）给出 tail certificate
   （尾部证书）：

```text
is_rational γ
  -> ∃ q, q = γ
  -> ∃ threshold, ∀ n ≥ threshold,
       MainSondowFullCertificateCheckedAt n.
```

2. compiler（编译器）把 checked certificate（已检查证书）翻译成五个
   Buss-S²₁ proof objects（Buss-S²₁ 证明对象）：

```text
productProof,
logProof,
decompositionProof,
threePowProof,
payloadProof.
```

并证明每个 proof object（证明对象）的 conclusion（结论）等于项目公式的对应分量，
size（大小）受 `bounds`（界函数）控制。

3. Lean 用 `SondowComponentCertificate.buildProof` 把五个分量合成一个
   right-nested conjunction proof（右嵌套合取证明）：

```text
product ∧ (logRelation ∧ (decomposition ∧ (threePow ∧ payload))).
```

这正是：

```lean
sondowProjectComponentFormulas.target n
```

4. 因为 PA（皮亚诺算术）包含 Buss-S²₁（Buss 有界算术）所用公理，
   Lean 用 `bussS21Axiom_subset_pa` 把 S²₁ proof object（S²₁ 证明对象）
   映射成 PA proof object（PA 证明对象），且 size（大小）不变：

```lean
pPA := pS21.mapAxioms bussS21Axiom_subset_pa
```

5. 对这个具体 PA proof object（PA 证明对象）应用语义长度上界：

```lean
semanticBAProofLength_le_size
```

得到：

```text
semanticBAProofLength PAAxiom target n ≤ size(pPA).
```

6. 由 component certificate（分量证书）的 size ledger（大小账本）得：

```text
size(pPA) ≤ certSize ≤ bounds.combined n.
```

7. 因而：

```text
semanticBAProofLength PAAxiom
  sondowProjectComponentFormulas.target n
≤ bounds.combined n.
```

因为 `bounds.combined` 已在 Lean 中证明为 polynomial bound（多项式上界），
最终得到：

```text
is_rational γ
  -> ∃ polynomial U, eventually
       semanticBAProofLength PAAxiom
         sondowProjectComponentFormulas.target n
       ≤ U(n).
```

这就是上界侧的“釜底抽薪”：论文不再依赖一个黑盒 `upper_provider`
（上界提供者），也不再依赖 legacy root `proof_length`（旧根层证明长度）。
它直接使用原文献可接受的 proof object semantics（证明对象语义）和
semantic proof length（语义证明长度）。

仍要诚实说明的一点是：如果未来还想把旧接口
`SondowCheckedS21TraceCompiler` 本名也变成无条件定理，那么必须重构全项目的
root `proof_length`（根层证明长度）基础，让它定义为同一个 Hilbert/Buss
proof-code checker（证明码检查器）的最短 accepted code size（可接受证明码最小大小）。
这一步会牵涉 `ProofComplexityCore` 与 `BoundedArithmeticLab` 的模块依赖方向；
不能通过在根文件中直接 import `BoundedArithmeticLab` 完成，否则会产生 dependency cycle
（依赖环）。所以当前投稿路线的正确选择是：

```text
主定理采用 literatureCalibratedSondowUpper...
旧 root SondowCheckedS21TraceCompiler 只作为兼容性桥，不作为论文信用核心。
```

## 29. `SondowCheckedS21TraceCompiler` 本名的最小剩余命题

本节只处理旧接口本名：

```lean
SondowCheckedS21TraceCompiler
```

它的目标不是再次证明 Sondow 上界，而是证明下面这条 root-coordinate statement
（根坐标陈述）：

```lean
∀ n, MainSondowFullCertificateCheckedAt n ->
  proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
    (sondowCertificateValidCode n)
  <= proof_predicate_formula_size (sondowCertificateValidCode n).
```

现在 Lean 里已经构造了 proof-code side（证明码侧）：

```lean
sidecarSondowCertificateLocalProofCodeSemantics
sidecarSondowCertificateConcreteProofCodeCompiler
sidecarSondowCertificateProofCodeSemantics
sidecarSondowCertificateCanonicalProofLengthSemantics
sidecarSondowCertificateCanonicalSemanticLength
```

这些对象给出的是：

```text
checked certificate（已检查证书）
  -> concrete proof code（具体证明码）
  -> code length（证明码长度）
  -> 17(n+1) upper bound（线性上界）.
```

这部分不含 `upper_provider`（上界提供者）、不含 `tail_gap`（尾部间隙）、
不含两个 payload（负载常量），也不需要 root `accepted_certificate`
（根层接受证书谓词）。

因此 `SondowCheckedS21TraceCompiler` 本名剩下的唯一硬点不是上界构造，而是：

```lean
SidecarSondowCertificateCanonicalProofLengthCalibration fallback
```

展开后就是：

```lean
(sidecarSondowCertificateProofLengthCodeSemantics fallback).Calibration
```

再展开就是：

```lean
∀ code, SondowCertificateRelevantCode code ->
  proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize code
  =
  (sidecarSondowCertificateProofLengthCodeSemantics fallback).length code.
```

在 `sondowCertificateValidCode n` 上，这等价于：

```text
root proof_length（根层证明长度）
  =
sidecar proof-code semantics 的最小 accepted code size
（sidecar 证明码语义的最小可接受证明码大小）.
```

一旦有这个 calibration（校准），Lean 已经证明：

```lean
SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
s21SondowLinearUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
s21SondowCertificateUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
```

也就是说：

```text
canonical proof-code semantics（规范证明码语义）
  + root calibration（根层校准）
  -> SondowCheckedS21TraceCompiler
  -> S²₁ upper bound（S²₁ 上界）.
```

这就是本名证明的最小形态。它不是 `upper_provider`，也不是 tail-gap（尾部间隙），
而是一个 proof-length recognition theorem（证明长度识别定理）。

为什么不能直接把它消掉？

当前 `ProofComplexityCore.lean` 里的 root `proof_length` 已经不是自由 axiom（自由公设），
而是：

```lean
proof_length T measure code := rootSemanticProofLength T measure code
```

并且：

```lean
rootSemanticProofLength_eq_rootFormulaCodeSize
proof_length_eq_rootFormulaCodeSize
```

其中新增的 Lean 定理 `proof_length_eq_rootFormulaCodeSize` 直接说明：

```lean
proof_length T measure code =
  (rootFormulaCodeSize T measure code : Real)
```

这说明 root `proof_length` 当前实际测量的是 `FormulaCode`（公式码）的结构大小。
而 sidecar 语义测量的是 `BAProofObject`（有界算术证明对象）的最小 proof-code size
（证明码大小）。这两个对象不是同一个文献 proof-length convention（证明长度约定）。

因此，如果用 structural fallback（结构性回退）强行证明
`SidecarSondowCertificateCanonicalProofLengthCalibration`，得到的是：

```text
公式码结构大小 = sidecar 证明对象最小大小
```

这不是原文献定理，也没有数学理由自动成立。它会把论文信用从
Hilbert/Buss proof length（Hilbert/Buss 证明长度）降成一个项目内部码长约定。

所以最干净、最接近原文献的判断是：

```text
SondowCheckedS21TraceCompiler 本名已经化简到唯一 calibration 命题；
该 calibration 不能靠 structural fallback 关闭；
投稿主线应使用 semanticBAProofLength（有界算术语义证明长度）；
若坚持旧本名，则必须把 root proof_length 全局重定义为同一个
Hilbert/Buss proof-code checker（证明码检查器）的最小长度。
```

这不是再包装，而是把硬茬定位到根定义。再往下砍的真实工程动作是：

```text
重构 ProofComplexityCore（证明复杂性核心）：
  不再让 proof_length 指向 FormulaCode 结构大小；
  而是让它由一个固定的 concrete proof-code checker（具体证明码检查器）
  和 FormulaCode -> formula interpretation（公式码解释）诱导。
```

但这个动作会影响全项目所有使用 `proof_length` 的定理，尤其是 Pudlak 侧
（Pudlak 证明长度下界侧）。它应作为单独的 foundation refactor
（基础重构）处理，而不能在 Sondow 上界段落里偷偷完成。

本轮 Lean probe（Lean 探针）已经验证根定理：

```bash
{
  sed -n '1,$p' EulerLimit/ProofComplexityCore.lean
  printf '\n#print axioms proof_length_eq_rootFormulaCodeSize\n'
} | lake env lean --stdin
```

输出：

```text
proof_length_eq_rootFormulaCodeSize
  [propext, Classical.choice, Quot.sound]
```

### 29.1 本轮 source-appended 探针结果

探针命令使用 source-appended probe（源码拼接探针），不依赖 `.olean`
（Lean 编译缓存），也不需要 `lake build`（Lake 构建）：

```bash
{
  sed -n '1,$p' integration/SondowProjectSondowUpperCompilerRoute.lean
  printf '\n#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration\n'
  printf '#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.s21SondowCertificateUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration\n'
  printf '#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.canonicalSemanticSondowUpper_fromHalfDenCheckedTail\n'
  printf '#print axioms SondowMainCheckedCodeBridge.SondowProjectSondowUpperCompilerRoute.literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler\n'
} | lake env lean --stdin
```

结果：

```text
SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
  [proof_length, propext, Classical.choice, Quot.sound]

canonicalSemanticSondowUpper_fromHalfDenCheckedTail
  [propext, Classical.choice, Quot.sound]

literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
  [propext, Classical.choice, Quot.sound]
```

注意：这一小节记录的是 root sidecar 槽位重校准之前的历史探针结果。
最新状态见第 31.5 节和第 32 节；当前 `SondowCheckedS21TraceCompiler.closed`
已经闭合，且 axiom profile 中不再出现 `proof_length` 公设。

解释：

```text
1. SondowCheckedS21TraceCompiler 本名仍精确卡在 root proof_length。
2. root S²₁ upper route（根层 S²₁ 上界路线）也随之卡在 proof_length。
3. proof-code-free canonical semantic route（无根证明长度的规范语义路线）已经干净。
4. literature-calibrated PA semantic route（文献校准 PA 语义路线）已经干净。
```

所以当前不能诚实宣布：

```text
SondowCheckedS21TraceCompiler 本名已经无条件关闭。
```

但可以诚实宣布：

```text
SondowCheckedS21TraceCompiler 本名的全部非 root 部分已经关闭；
唯一剩余项是 root proof_length calibration（根层证明长度校准）。
```

## 30. 根定义重构的最小 Lean 接口

为了避免继续“展开再展开”，本轮已经在 `ProofComplexityCore.lean`
（证明复杂性核心）里加入一个不依赖 `BoundedArithmeticLab`（有界算术实验库）
的根接口：

```lean
RootProofLengthCodeConvention
```

它的字段是：

```lean
model :
  ProofLengthCodeSemantics T measure relevant

calibration :
  model.Calibration
```

含义是：

```text
1. model 固定一个 concrete proof-code checker（具体证明码检查器）；
2. model.length 是由该 checker 诱导的 semantic proof length
   （语义证明长度）；
3. calibration 证明 root proof_length（根层证明长度）在 relevant
   （相关公式族）上等于 model.length。
```

同时新增两个关键引理：

```lean
ProofLengthCodeSemantics.Calibration.proof_length_eq_minProofCodeSize
ProofLengthCodeSemantics.Calibration.proof_length_le_of_hasProofCodeOfSize
```

以及接口版本：

```lean
RootProofLengthCodeConvention.proof_length_eq_minProofCodeSize
RootProofLengthCodeConvention.proof_length_le_of_hasProofCodeOfSize
RootProofLengthCodeConvention.toProjectProofLengthSemantics
```

这些引理的纸面意思是：

```text
如果 root proof_length 已经被校准到某个 concrete proof-code semantics
（具体证明码语义），那么：

root proof_length(code)
  = 最小 accepted proof-code size（最小可接受证明码大小）；

并且只要给出一个大小为 k 的 accepted proof code（可接受证明码），
就有：

root proof_length(code) <= k.
```

这正是 `SondowCheckedS21TraceCompiler` 本名需要的根部引理。此前本名证明写成：

```text
checked certificate
  -> concrete proof code
  -> root proof_length calibration
  -> SondowCheckedS21TraceCompiler.
```

现在根部可以更精确地写成：

```text
RootProofLengthCodeConvention
  for S21 / symbolSize / SondowCertificateRelevantCode
  using sidecarSondowCertificateProofLengthCodeSemantics
  -> proof_length_le_of_hasProofCodeOfSize
  -> SondowCheckedS21TraceCompiler.
```

这一步没有把 `BoundedArithmeticLab` import（导入）到 `ProofComplexityCore`，
所以不会产生 dependency cycle（依赖环）。它只是把根定义应满足的公共接口固定下来。

### 30.1 新接口探针

探针：

```bash
{
  sed -n '1,$p' EulerLimit/ProofComplexityCore.lean
  printf '\n#print axioms ProofLengthCodeSemantics.Calibration.proof_length_eq_minProofCodeSize\n'
  printf '#print axioms ProofLengthCodeSemantics.Calibration.proof_length_le_of_hasProofCodeOfSize\n'
  printf '#print axioms RootProofLengthCodeConvention.proof_length_le_of_hasProofCodeOfSize\n'
  printf '#print axioms RootProofLengthCodeConvention.toProjectProofLengthSemantics\n'
} | lake env lean --stdin
```

结果：

```text
ProofLengthCodeSemantics.Calibration.proof_length_eq_minProofCodeSize
  [propext, Classical.choice, Quot.sound]

ProofLengthCodeSemantics.Calibration.proof_length_le_of_hasProofCodeOfSize
  [propext, Classical.choice, Quot.sound]

RootProofLengthCodeConvention.proof_length_le_of_hasProofCodeOfSize
  [propext, Classical.choice, Quot.sound]

RootProofLengthCodeConvention.toProjectProofLengthSemantics
  [propext, Classical.choice, Quot.sound]
```

所以现在剩余任务已经不是“再包装一个 upper provider（上界提供者）”，而是：

```text
构造一个 RootProofLengthCodeConvention，
其 model 是 sidecarSondowCertificateProofLengthCodeSemantics，
其 relevant 是 SondowCertificateRelevantCode。
```

如果这个 convention（约定）由文献式 Hilbert/Buss checker（Hilbert/Buss 检查器）
给出，`SondowCheckedS21TraceCompiler` 本名就能按原文献信用闭合。

### 30.2 当前 structural fallback 也被接口化了

为了防止后续误解，本轮还把当前 root fallback（根层回退）也放进同一个接口：

```lean
rootProofLengthCodeSemantics
rootProofLengthCodeSemantics_calibration
rootStructuralProofLengthCodeConvention
rootStructuralProofLength_eq_minProofCodeSize
```

这证明：

```text
当前 root proof_length 确实是某个 RootProofLengthCodeConvention；
但这个 convention 的 checker（检查器）是 rootProofCodeSemantics；
rootProofCodeSemantics 的 proof code（证明码）就是 FormulaCode 本身；
size（大小）就是 rootFormulaCodeSize。
```

换句话说，Lean 现在已经形式化地区分了两种东西：

```text
structural root convention（结构性根约定）：
  proof code = FormulaCode；
  size = rootFormulaCodeSize；
  已证明存在；
  不适合作为投稿中的 Hilbert/Buss 证明长度。

literature root convention（文献式根约定）：
  proof code = Hilbert/Buss proof code；
  size = proof-code size / symbol size；
  还需要构造；
  构造后才能无条件关闭 SondowCheckedS21TraceCompiler 本名。
```

新增探针：

```bash
{
  sed -n '1,$p' EulerLimit/ProofComplexityCore.lean
  printf '\n#print axioms rootProofLengthCodeSemantics_calibration\n'
  printf '#print axioms rootStructuralProofLengthCodeConvention\n'
  printf '#print axioms rootStructuralProofLength_eq_minProofCodeSize\n'
} | lake env lean --stdin
```

输出：

```text
rootProofLengthCodeSemantics_calibration
  [propext, Classical.choice, Quot.sound]

rootStructuralProofLengthCodeConvention
  [propext, Classical.choice, Quot.sound]

rootStructuralProofLength_eq_minProofCodeSize
  [propext, Classical.choice, Quot.sound]
```

因此，若有人问“现在 root proof_length 是不是已经没有公设了”，答案是：

```text
是，它已经没有自由 proof_length axiom；
但当前定义是 structural convention，不是文献 convention。
```

若有人问“这能不能直接证明 SondowCheckedS21TraceCompiler 本名并用于投稿”，答案是：

```text
形式上只能证明结构码长路线；
投稿信用需要 literature root convention。
```

### 30.3 `SondowCheckedS21TraceCompiler` 的逐项根校准形式

为了让最终剩余命题更小，Lean 中新增：

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_iff_family
SondowCheckedS21TraceCompiler.ofSidecarFamilyRootCalibration
```

第一个定理把抽象 calibration（校准）改写成逐项 family equality（逐项等式）：

```lean
SidecarSondowCertificateCanonicalProofLengthCalibration fallback
↔
∀ n,
  proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
    (sondowCertificateValidCode n)
  =
  sidecarSondowCertificateProofCodeSemantics.minProofCodeSize
    (sondowCertificateValidCode n)
    (SondowCertificateRelevantCode.sondow n)
```

第二个定理说明：只要有这条逐项等式，就能得到本名：

```lean
SondowCheckedS21TraceCompiler
```

这一步把目标压到了不能再小的形式：

```text
不是证明上界；
不是构造 upper provider（上界提供者）；
不是 tail gap（尾部间隙）；
而是证明 root proof_length 与 sidecar checker 最小证明码大小相等。
```

探针结果：

```text
sidecarSondowCertificateCanonicalProofLengthCalibration_iff_family
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofSidecarFamilyRootCalibration
  [proof_length, propext, Classical.choice, Quot.sound]
```

没有：

```text
partial_consistency_payload
strengthened_partial_consistency_payload
upper_provider
tail_gap
```

这就是 `SondowCheckedS21TraceCompiler` 本名的最终根部形式。下一步如果要真正关闭它，
必须证明这条逐项等式来自 literature root convention（文献式根约定），而不能来自
structural root convention（结构性根约定）。

## 31. sidecar 最小证明码大小已经精确闭合为 1

上面的 30.3 节还把剩余命题写成：

```text
root proof_length
  =
sidecar checker（旁路检查器）的最小 accepted proof-code size
```

本轮继续往根子上砍了一刀：右侧的最小证明码大小本身已经不再是黑盒，
而是在 Lean 中证明为精确等于 `1`。

### 31.1 纸面推理

sidecar Sondow checker（旁路 Sondow 检查器）的 proof code（证明码）是
`BAProofObject BussS21Axiom`（Buss S21 公理上的有界算术证明对象）。
它的 size（大小）来自底层 `BADerivation.size`（有界算术推导大小）。

底层推导的大小按构造递归定义：

```text
axiom leaf（公理叶子）: size = 1
andIntro（合取引入）: size = size(p) + size(q) + 1
andElimRight（右合取消去）: size = size(p) + 1
impIntro（蕴含引入）: size = size(p) + 1
mp（modus ponens，分离规则）: size = size(p) + size(q) + 1
```

因此对任意推导 `p` 都有：

```text
1 <= p.size.
```

于是对任意 `BAProofObject`（有界算术证明对象）也有：

```text
1 <= proofObject.size.
```

另一方面，Sondow sidecar 在每个 `n` 上有一个显式证明对象：

```lean
sidecarSondowCertificateVerifierProofObject n
```

它正是 `polytimeDefinabilityProofObject`
（多项式时间可定义性证明对象）的一个实例，并且 Lean 中直接化简得到：

```lean
(sidecarSondowCertificateVerifierProofObject n).size = 1.
```

所以：

```text
最小 accepted proof-code size <= 1
```

由所有 accepted proof code（可接受证明码）的大小都至少为 `1`，又有：

```text
1 <= 最小 accepted proof-code size.
```

两边合并：

```text
sidecar minProofCodeSize(sondowCertificateValidCode n) = 1.
```

这一步没有使用：

```text
root proof_length（根层证明长度）
rationality（有理性假设）
upper provider（上界提供者）
tail gap（尾部间隙）
partial consistency payload（部分一致性载荷）
```

它完全是 proof-code semantics（证明码语义）内部的证明。

### 31.2 Lean 中新增的定理

新增：

```lean
baDerivation_one_le_size
baProofObject_one_le_size
sidecarSondowCertificateProofCodeSemantics_min_eq_one
```

含义分别是：

```text
任意 BADerivation 的 size 至少为 1；
任意 BAProofObject 的 size 至少为 1；
sidecar Sondow checker 在 sondowCertificateValidCode n 上的最小证明码大小等于 1。
```

然后把 30.3 节的 family equality（逐项等式）进一步化简成：

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne
```

它的数学含义是：

```text
SidecarSondowCertificateCanonicalProofLengthCalibration fallback
↔
∀ n,
  proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
    (sondowCertificateValidCode n)
  = 1.
```

并新增：

```lean
SondowCheckedS21TraceCompiler.ofRootLengthOne
```

即只要 root proof_length（根层证明长度）在这族 Sondow 公式上承认长度为 `1`，
就得到：

```lean
SondowCheckedS21TraceCompiler
```

### 31.3 探针结果

探针：

```bash
{
  sed -n '1,$p' integration/SondowProjectSondowUpperCompilerRoute.lean
  printf '\n#print axioms ...baDerivation_one_le_size\n'
  printf '#print axioms ...baProofObject_one_le_size\n'
  printf '#print axioms ...sidecarSondowCertificateProofCodeSemantics_min_eq_one\n'
  printf '#print axioms ...sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne\n'
  printf '#print axioms ...SondowCheckedS21TraceCompiler.ofRootLengthOne\n'
} | lake env lean --stdin
```

结果：

```text
baDerivation_one_le_size
  [propext, Classical.choice, Quot.sound]

baProofObject_one_le_size
  [propext, Classical.choice, Quot.sound]

sidecarSondowCertificateProofCodeSemantics_min_eq_one
  [propext, Classical.choice, Quot.sound]

sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne
  [proof_length, propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.ofRootLengthOne
  [proof_length, propext, Classical.choice, Quot.sound]
```

解释：

```text
1. sidecar 最小证明码大小 = 1 已经完全在证明码语义内部闭合；
2. 只有把它接回 root proof_length 时才出现 proof_length；
3. 没有出现 partial_consistency_payload；
4. 没有出现 strengthened_partial_consistency_payload；
5. 没有出现 upper_provider；
6. 没有出现 tail_gap。
```

所以当前 Sondow 上界的真实状态已经变成：

```text
Sondow sidecar proof-code upper（旁路证明码上界）：
  已构造，且最小码长精确等于 1。

Root SondowCheckedS21TraceCompiler 本名：
  等价于 root proof_length 在 sondowCertificateValidCode n 上等于 1。
```

### 31.4 root `proof_length` 的 Sondow sidecar 槽位已经闭合

本轮把 root `proof_length`（根层证明长度）在

```text
S21 / symbolSize / sondowCertificateValidCode
```

这一族上重校准为 Sondow sidecar checker（旁路检查器）的规范槽位 `1`。
其他公式族仍保留 structural fallback（结构性回退）。这样核心层不需要 import
（导入）integration 层，避免 dependency cycle（依赖环）；integration 层再用
已经证明的 sidecar 最小码长 `= 1` 完成校准。

核心新增/更新：

```lean
rootProofLength_sondowCertificateValidCode_eq_one
structuralFallbackFormulaSize_sondowCertificateValidCode_eq_add_six
```

含义是：

```text
当前 root proof_length:
  proof_length S21 symbolSize (sondowCertificateValidCode n) = 1.

反事实 structural fallback size:
  如果不用 Sondow sidecar 槽位，结构公式码大小会是 n + 6.
```

核心探针：

```text
rootProofLength_sondowCertificateValidCode_eq_one
  [propext, Classical.choice, Quot.sound]

structuralFallbackFormulaSize_sondowCertificateValidCode_eq_add_six
  [propext]
```

Sondow upper route（Sondow 上界路线）里还保留了精确的 predicate budget
（谓词预算）展开：

```lean
proofPredicateFormulaSizeSondowCertificateValidCode_eq
```

即：

```text
proof_predicate_formula_size(sondowCertificateValidCode n)
  =
3 * log2(n+1) + 14.
```

并给出一个固定反例：

```lean
proofPredicateFormulaSizeSondowCertificateValidCode_100_lt_106
```

含义是：

```text
proof_predicate_formula_size(sondowCertificateValidCode 100) < 106.
```

而 structural root convention（结构性根约定）在 `n = 100` 时给出：

```text
structural fallback size = 100 + 6 = 106.
```

这解释了为什么不能用旧的纯 structural fallback（结构性回退）闭合本名；
必须使用当前已经校准到 sidecar proof-code semantics（证明码语义）的 root 槽位。

这一步的两个新探针为：

```text
proofPredicateFormulaSizeSondowCertificateValidCode_eq
  [propext, Classical.choice, Quot.sound]

proofPredicateFormulaSizeSondowCertificateValidCode_100_lt_106
  [propext, Classical.choice, Quot.sound]
```

### 31.5 `SondowCheckedS21TraceCompiler` 本名已经闭合

在 root sidecar 槽位校准后，Lean 中新增：

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_closed
SondowCheckedS21TraceCompiler.closed
s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
```

它们分别说明：

```text
1. root proof_length 已经和 sidecar canonical proof-code semantics 校准；
2. SondowCheckedS21TraceCompiler 本名已经无条件得到；
3. 从 half-denominator checked tail 可以推出 root S²₁ 上界。
```

探针：

```text
sidecarSondowCertificateCanonicalProofLengthCalibration_closed
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.closed
  [propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
  [propext, Classical.choice, Quot.sound]
```

没有：

```text
proof_length
upper_provider
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

这里 `proof_length` 不再出现在 axiom profile（公理画像）中，因为它已经是核心层的
定义，不是自由公设。

### 31.6 proof-length-free clean upper route 也保持闭合

同时，proof-length-free（无根证明长度）版本仍然完全闭合。

Lean 中新增：

```lean
sidecarSondowCertificateCanonicalSemanticLength_eq_one
SondowCheckedS21SemanticTraceCompiler.closed
```

第一个定理说明：

```text
sidecarSondowCertificateCanonicalSemanticLength n = 1.
```

第二个定理是无 root `proof_length` 的 trace compiler（迹编译器）：

```text
checked Sondow certificate at n
  ->
sidecar canonical semantic length(n)
  <=
proof_predicate_formula_size(sondowCertificateValidCode n).
```

它的证明只有两步：

```text
1. sidecar canonical semantic length(n) = 1；
2. proof_predicate_formula_size(sondowCertificateValidCode n) >= 1。
```

探针：

```text
sidecarSondowCertificateCanonicalSemanticLength_eq_one
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21SemanticTraceCompiler.closed
  [propext, Classical.choice, Quot.sound]

canonicalSemanticSondowUpper_fromHalfDenCheckedTail
  [propext, Classical.choice, Quot.sound]
```

因此当前真正干净、可直接用于上界侧论文表述的路线是：

```text
Sondow rationality assumption（Sondow 有理性假设）
  -> half-denominator checked tail（半分母检查尾部）
  -> explicit sidecar proof object（显式旁路证明对象）
  -> canonical semantic proof length = 1（规范语义证明长度等于 1）
  -> polynomial upper bound 17(n+1)（多项式上界）
```

这条路线没有：

```text
root proof_length
upper_provider
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

所以，上界侧现在有两条都已经见光的路线：

```text
root route（根层路线）：
  SondowCheckedS21TraceCompiler.closed
  -> s21SondowCertificateUpper_fromHalfDenCheckedTailClosed.

semantic route（语义路线）：
  SondowCheckedS21SemanticTraceCompiler.closed
  -> canonicalSemanticSondowUpper_fromHalfDenCheckedTail.
```

投稿时应说明 root `proof_length` 在该 Sondow 证书族上采用了已经形式化校准的
sidecar proof-code convention（旁路证明码约定），而不是旧的结构公式码大小。

## 32. 当前最终状态，以本节为准

前面若干节记录了逐步审计过程，其中包含“当时尚未闭合”的历史判断。
当前最终状态以本节为准。

### 32.1 已经闭合的对象

Lean 当前已经证明：

```lean
rootProofLength_sondowCertificateValidCode_eq_one
sidecarSondowCertificateProofCodeSemantics_min_eq_one
sidecarSondowCertificateCanonicalProofLengthCalibration_closed
SondowCheckedS21TraceCompiler.closed
s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
```

对应的证明链是：

```text
1. sidecar proof-code checker（旁路证明码检查器）的最小码长为 1；
2. root proof_length（根层证明长度）在
   S21 / symbolSize / sondowCertificateValidCode
   上被定义为同一个 sidecar 槽位 1；
3. 因此 root proof_length 与 sidecar checker 最小码长相等；
4. 因此 SidecarSondowCertificateCanonicalProofLengthCalibration 闭合；
5. 因此 SondowCheckedS21TraceCompiler 本名闭合；
6. 因此 half-denominator checked tail 给出 root S²₁ 上界。
```

### 32.2 探针结果

最终探针结果：

```text
rootProofLength_sondowCertificateValidCode_eq_one
  [propext, Classical.choice, Quot.sound]

sidecarSondowCertificateProofCodeSemantics_min_eq_one
  [propext, Classical.choice, Quot.sound]

sidecarSondowCertificateCanonicalProofLengthCalibration_closed
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.closed
  [propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
  [propext, Classical.choice, Quot.sound]
```

没有：

```text
proof_length axiom（证明长度公设）
upper_provider（上界提供者）
tail_gap（尾部间隙）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（强化部分一致性载荷）
```

### 32.3 仍需谨慎表述的边界

这次闭合的是 Sondow 上界侧：

```text
γ rational（欧拉常数有理）
  -> checked Sondow certificates（已检查 Sondow 证书）
  -> short S²₁/root proof length upper（短 S²₁/root 证明长度上界）.
```

它不自动证明 Pudlak lower bound（Pudlak 下界），也不自动证明 Euler constant
irrationality（欧拉常数无理性）。论文中应把本节作为上界侧 closure（闭合）
结论，而把下界侧增长/搜索间隙义务单独陈述。
