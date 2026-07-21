# 基础数学有效性独立计算检查记录

日期：2026-07-19

工作目录：`/home/james/code/sondow-pudlak-bigN-audit-20260708/sondow-pudlak-collision-box-bigN-halfden-full-20260708`

## 1. 范围、状态词与结论

本记录只检查交接单第四阶段附加所列的纯算术部分：

1. `rho_d(n)=(n+1)^(d n)` 的完美幂恒等式、取整、阈值和单调性；
2. 从固定正幂下界到 `(n+1)^n` 的指数选择和严格不等式方向；
3. `n >= max(3,ceil(q/2))` 的 half-denominator 阈值；
4. PA 编译器中载荷多项式的加法、乘法、复合和单调代入方向；
5. `rho_d(n)` 的数值、二进制位长、公式码数值和完整载荷长度之间的方向；
6. 缺少正性、严格性、向上取整或哨兵位时的有限反例。

状态词严格按以下含义使用：

- `PASS_EXACT`：SymPy 对一个具体多项式恒等式或精确系数展开返回精确结果；
- `FAIL`/`COUNTEREXAMPLE`：预期成立的检查失败；脚本以非零状态退出；
- `SAMPLE_ONLY`：只在明示的有限整数盒中没有找到反例，**不是证明**；
- `EXPECTED_COUNTEREXAMPLE`：找到了故意削弱假设后的精确有限反例；
- `🟨 YELLOW_UNRESOLVED`：后端没有解决无界量化命题，或相应后端没有安装；
- `🟨 YELLOW_SCOPE`：命题原则上超出 CAS 的验证能力。
- `INCOMPLETE_YELLOW`：Wolfram 至少有一项未求解或超时；脚本以状态 `2` 退出，绝不
  把黄色项汇总成通过。

计算结论是：所有已单独给出纸面证明的纯算术命题与 SymPy 精确展开相容，有限搜索
没有发现满足完整假设的反例；搜索同时找到了八类常见错误方向的反例。这个结论不把
有限抽样升级为证明，也不改变总路线中逻辑桥的审计判决。

## 2. 后端探测、版本和复现命令

实际执行：

```bash
command -v wolframscript || true
command -v WolframKernel || true
command -v math || true
python3 --version
python3 - <<'PY'
import sympy
print(sympy.__version__)
PY
```

完整输出（前三个 `command -v` 均为空）：

```text
Python 3.12.3
1.14.0
```

因此本机未检测到 `wolframscript`、`WolframKernel` 或兼容的 `math` 命令；
Wolfram 脚本已经生成，但没有伪造运行结果。实际使用的独立后端正是交接单指定的
SymPy `1.14.0`。

Wolfram 复现命令（待有 Wolfram Engine 的环境执行）：

```bash
set -o pipefail
wolframscript -file scripts/foundational_mathematical_validity_checks.wls \
  | tee /tmp/foundational_mathematical_validity_checks_wolfram.out
```

SymPy 实际执行命令：

```bash
set -o pipefail
python3 scripts/foundational_mathematical_validity_checks_sympy.py \
  | tee /tmp/foundational_mathematical_validity_checks_sympy.out
```

最终复核运行退出码为 `0`，墙钟时间 `2.93s`；标准输出与第 5 节逐字 `diff` 为空。
两个精确输入脚本在本次运行后的 SHA-256 为：

```text
d58c2366aa90e488b550f924834302130d388044ebe1b7371cd4e67bad4a815b  scripts/foundational_mathematical_validity_checks.wls
6b63fc932fc77ba9bf2c660b1b6945922fcca8280fb2cc3fcacfa8d7f368b513  scripts/foundational_mathematical_validity_checks_sympy.py
```

两个脚本均不调用浮点近似。SymPy 搜索使用 Python 任意精度整数和
`sympy.Rational`；Wolfram 输入只使用 `Integers`、`Rationals`、精确幂、
`FullSimplify`、`Refine`、`Reduce`、`Resolve` 和 `FindInstance`。
两份脚本对非预期反例/明确 `False` 均 fail-closed；Wolfram 的潜在长计算有 60 秒
`TimeConstrained`，超时明确标作 `YELLOW_UNRESOLVED`，总体状态为
`INCOMPLETE_YELLOW` 而不是 `PASS`。
Wolfram API 形状还与官方的 [FindInstance](https://reference.wolfram.com/language/ref/FindInstance.html)、
[FindEquationalProof](https://reference.wolfram.com/language/ref/FindEquationalProof.html)、
[ProofObject](https://reference.wolfram.com/language/ref/ProofObject.html) 和
[CoefficientRules](https://reference.wolfram.com/language/ref/CoefficientRules.html) 文档核对过。

## 3. 输入命题和纸面核对

### 3.1 `rho`、固定正幂和阈值

令

```text
R(n) = (n+1)^n,
rho_d(n) = (n+1)^(d n).
```

对 `d,n` 为自然数，有

```text
rho_d(n) = R(n)^d,
rho_(d+1)(n) = rho_d(n) R(n),
d(n+1)=dn+d.
```

这些等式只用自然数幂律和乘法交换律，不使用分数次幂。若 `d>=1`，则
`rho_d` 严格递增：`n=0` 时 `rho_d(0)=1<2^d=rho_d(1)`；`n>=1` 时

```text
rho_d(n+1)
  = (n+2)^(dn+d)
  > (n+1)^(dn+d)
  = rho_d(n)(n+1)^d
  > rho_d(n).
```

所以从某个关于原参数 `b` 的阈值 `B0` 重标定时，保守选择外层阈值 `n>=B0`
已经保证 `rho_d(n)>=B0`。这不是最小阈值，但方向正确且完全显式。

若原下界指数为正有理数 `alpha=a/c`，其中 `a,c>=1`，取

```text
d = ceil(c/a).
```

则 `ad>=c`，从而

```text
rho_d(n)^a = (n+1)^(adn) >= (n+1)^(cn) = R(n)^c.
```

若原定理给出严格下界 `M(b)>b^(a/c)`，等价地用正整数幂比较，就得到
`M(rho_d(n))>R(n)`。若只给非严格下界，最后的严格目标并不自动成立；有限反例
`M=R=1, c=1` 已在脚本中主动检出。

对于任意正实指数 `alpha`，同一选择原则写作 `d>=1/alpha`。纯代数恒等式

```text
alpha*d - 1 = alpha*(d - 1/alpha)
```

说明 `alpha>0` 时右侧非负。真正使用任意实数幂时还必须在纸面证明中写明正底数
和实幂律；当前完美幂/正整数幂表述避免了这个不必要的分支问题。

### 3.2 `(n+1)^n` 超过固定多项式的显式阈值

若

```text
U(n) <= c (n+1)^k,  c>=0,
```

取自然数 `C>=c`。对 `n>=C+k+1`，令 `B=n+1`。则 `C<B`、`B^k>0`、
`k+1<=n`，所以

```text
U(n) <= c B^k <= C B^k < B^(k+1) <= B^n = (n+1)^n.
```

这正是 `FoundationPudlakBussRescaledLowerBoundGate.lean` 中采用的保守阈值。
削弱成 `n>=C+k-1` 不成立，例如 `(C,k,n)=(1,0,0)` 给出 `1<1`。

### 3.3 half-denominator 阈值

对非负整数 `q`，

```text
ceil(q/2) = (q+1)//2,
n >= ceil(q/2)  iff  q <= 2n.
```

因此 `n>=max(3,ceil(q/2))` 同时给出 `n>=3` 和 `q<=2n`。不能把
`ceil` 换成 `floor`：`q=1,n=0=floor(q/2)` 时 `q<=2n` 为假。

这里的 `q` 是有理性见证的正分母时结论当然仍成立；脚本还检查了允许 `q=0` 的
更宽纯算术版本。

### 3.4 载荷多项式的组合

脚本逐项录入了当前 PA 定量编译器中的以下局部形状：

```text
specializationCost(s) = 192 + 2048 s^3
modusPonensBound(L,R,s) = L + R + 240 + 34s
conjunctionBound(L,R,s) = L + R + 144 + 11s
existsBound(L,s) = L + 96 + 14s
connectorBound(r,t) = 1024 + 256(r+t+1)
nodePayloadBound(r,L,t) = r(L+connectorBound(r,t)+1).
```

精确展开的所有系数非负。因此在所有参数非负时，每个形状对每个参数单调；把
`L<=P(r)`、`R<=Q(r)`、`s<=S(r)` 代入右端的方向是“原界不超过代入后的界”。
`Resolve`/`Reduce` 在 Wolfram 脚本中明确检查了 MP 和乘法代入的实闭域版本。

对非负系数多项式 `P,Q`，加法、乘法和复合仍有非负系数。脚本以符号系数模板

```text
P(z)=p0+p1 z+p2 z^2+p3 z^3,
Q(z)=q0+q1 z+q2 z^2
```

精确展开加、乘和 `P(Q(z))`；一般次数的纸面证明是有限卷积：每个新系数都是原
非负系数的有限和或有限积。累积包络还满足精确递推

```text
Sum(P(i),i=0..r+1)-Sum(P(i),i=0..r)=P(r+1).
```

若 `A,D,C,C0>=0`，`p,q,E` 为自然数（模拟开销场景中 `E>=1`），且检查器时间与
输入大小分别满足

```text
T(n)<=A(n+1)^p,  S(n)<=D(n+1)^q,
```

且证明模拟开销为 `C(T+S+1)^E`，令 `e=max(p,q)`，则因 `n+1>=1`，

```text
C(T+S+1)^E
 <= C(A+D+1)^E (n+1)^(eE).
```

这给出显式的复合多项式，而不只写“多项式对复合封闭”。同理，两个证明族和常数
嫁接时

```text
A(n+1)^p+D(n+1)^q+C0
 <= (A+D+C0)(n+1)^max(p,q).
```

这些结论仍以各底层 `T,S` 界已经真实建立为前提；CAS 不会构造那些逻辑对象。

### 3.5 公式码、数值大小和完整载荷长度的方向

项目定义是

```text
packedPayloadLength(code) = bit_length(code)-1.
```

对长为 `L` 的低位优先 payload bits，`packBinaryString` 在第 `L` 位添加一个
值为 `1` 的哨兵。因此精确有

```text
2^L <= packedCode < 2^(L+1),
bit_length(packedCode)=L+1,
packedPayloadLength(packedCode)=L.
```

这与现有内核定理 `size_packBinaryString` 及
`packedPayloadLength_packedCertifiedPAProofCode` 的方向相同。

对 `d>=1,n>=0`，

```text
bit_length(rho_d(n))
  <= 1 + d n bit_length(n+1).
```

当 `n>=1`（指数正）时可以去掉额外的 `1`；`n=0` 时右侧会变成 `0`，而
`bit_length(rho_d(0))=bit_length(1)=1`，所以统一陈述必须保留常数项或单独处理
`n=0`。又因 `bit_length(n+1)<=n+1`，固定 `d` 后该位长被
`1+d n(n+1)` 这个外层 `n` 的多项式支配。

必须强调，`rho_d(n)` 的**数值**是超多项式尺度，而其二进制数词的**位长**是
关于外层 `n` 的多项式。禁止反向写成 `rho_d(n)<=bit_length(rho_d(n))`；脚本给出
最小搜索反例之一 `(d,n)=(1,2)`，此时 `rho=27` 而位长为 `5`。同样，公式码数值
可能指数依赖其语法长度；证明长度界需要的是位长或完整 payload 长度，不能用裸
自然数码值代替。

## 4. 主动反例汇总

以下均为精确整数反例，不含浮点：

| 被削弱或反向的命题 | 反例 | 失败原因 |
|---|---:|---|
| 不要求 `d>0` 仍称 `rho_d` 严格递增 | `d=0,n=0` | `rho_0` 恒为 `1` |
| 不要求正幂次数仍反射次序 | `k=0,x=0,y=1` | 两边零次幂都为 `1` |
| 非严格幂下界推出严格目标 | `k=1,x=y=1` | 只能得到 `x>=y` |
| 用 `n>=C+k-1` 保证严格超越 | `C=1,k=0,n=0` | 得到假的 `1<1` |
| half-den 阈值用 `floor` 代替 `ceil` | `q=1,n=0` | `1<=0` 为假 |
| 正指数位长界直接用于指数零 | `d=1,n=0` | `1<=0` 为假 |
| 把数值 `rho` 压到自身位长 | `d=1,n=2` | `27<=5` 为假 |
| 底数不要求至少 `1` 仍按指数单调 | `base=0,e1=0,e2=1` | `1<=0` 为假 |

这些反例固定了纸面陈述中不可省略的正性、严格性、阈值和方向假设。

## 5. SymPy 完整标准输出

以下是上述已哈希输入脚本的完整标准输出；没有删节：

```text
SymPy version: 1.14.0
Arithmetic mode: exact Integer/Rational only; no Float objects constructed
PASS_EXACT | rho perfect-power exponent identity d*n=n*d | True
PASS_EXACT | rho_(d+1) exponent recurrence (d+1)n=dn+n | Eq(n*(d + 1), d*n + n)
PASS_EXACT | adjacent monotonicity comparison exponent d(n+1)=dn+d | Eq(d*(n + 1), d*n + d)
SAMPLE_ONLY | rho_d is strictly increasing in n when d>=1 | no counterexample in 1<=d<=8, 0<=n<m<=20
SAMPLE_ONLY | rho_(d+1)(n)=rho_d(n)*carrier(n) | no counterexample in 0<=d<=8, 0<=n<=20
SAMPLE_ONLY | rho_d(n+1)>=rho_d(n)*(n+1)^d | no counterexample in 1<=d<=8, 0<=n<=20
EXPECTED_COUNTEREXAMPLE | dropping d>0 makes strict rho monotonicity false | (0, 0)
YELLOW_UNRESOLVED | unbounded symbolic rho monotonicity | (n + 1)**(d*n) < (n + 2)**(d*(n + 1)) | variable integer exponents are outside SymPy's complete inequality procedures; see paper proof
PASS_EXACT | fixed-root perfect-power rewrite (x^(k*n))^1/k is avoided | rho_k(n)=carrier(n)^k by natural-power laws
SAMPLE_ONLY | rho_k(n)=carrier(n)^k | no counterexample in 1<=k<=8, 0<=n<=20
SAMPLE_ONLY | x^k>y^k implies x>y over naturals for k>0 | no counterexample in 1<=k<=8, 0<=x,y<=30
EXPECTED_COUNTEREXAMPLE | dropping k>0 invalidates root-order reflection | (0, 0, 1)
SAMPLE_ONLY | d=ceil(c/a) satisfies a*d>=c | no counterexample in 1<=a,c<=30
SAMPLE_ONLY | general rational exponent comparison rho_d(n)^a>=carrier(n)^c | no counterexample in 1<=a,c<=8, 0<=n<=12, d=ceil(c/a)
YELLOW_UNRESOLVED | symbolic ceiling implication a*ceil(c/a)>=c | a*ceiling(c/a) >= c | SymPy leaves the quantified ceiling fact conditional; the finite search is not its proof
PASS_EXACT | Archimedean exponent-choice algebra alpha*d-1=alpha*(d-1/alpha) | with alpha>0 and d>=1/alpha the right side is nonnegative
SAMPLE_ONLY | conservative rescaling threshold n>=B0 implies rho_d(n)>=B0 | no counterexample in 1<=d<=8, 0<=B0<=n<=30
EXPECTED_COUNTEREXAMPLE | a non-strict fixed-power lower bound cannot yield the strict target | (1, 1, 1)
SAMPLE_ONLY | explicit polynomial-domination threshold C+k+1 | no counterexample in 0<=C<=20, 0<=k<=8, C+k+1<=n<=C+k+5
EXPECTED_COUNTEREXAMPLE | weakened threshold n>=C+k-1 is insufficient | (1, 0, 0)
SAMPLE_ONLY | ceil(q/2)=(q+1)//2 for integer q>=0 | no counterexample in 0<=q<=500
SAMPLE_ONLY | n>=max(3,ceil(q/2)) implies q<=2n | no counterexample in 0<=q<=100, max(3,ceil(q/2))<=n<80
EXPECTED_COUNTEREXAMPLE | floor(q/2) cannot replace ceil(q/2) | (1, 0)
PASS_EXACT | nonnegative-coefficient polynomials close under addition | monomials=7
PASS_EXACT | nonnegative-coefficient polynomials close under multiplication | monomials=12
PASS_EXACT | nonnegative-coefficient polynomials close under composition | monomials=20
PASS_EXACT | specialization payload polynomial has only nonnegative coefficients | 2048*syntax**3 + 192
PASS_EXACT | modus-ponens payload polynomial has only nonnegative coefficients | proof_left + proof_right + 34*syntax + 240
PASS_EXACT | conjunction payload polynomial has only nonnegative coefficients | proof_left + proof_right + 11*syntax + 144
PASS_EXACT | existential-introduction payload polynomial has only nonnegative coefficients | proof_left + 14*syntax + 96
PASS_EXACT | bounded-formula connector envelope has only nonnegative coefficients | 256*resource + 256*syntax + 1280
PASS_EXACT | resource times node-envelope payload polynomial has only nonnegative coefficients | proof_left*resource + 256*resource**2 + 256*resource*syntax + 1281*resource
PASS_EXACT | cumulative-envelope recurrence Sum[0..r+1]-Sum[0..r]=B(r+1) | (r + 1)*(12*p0 + 6*p1*r + 4*p2*r**2 + 2*p2*r + 3*p3*r**3 + 3*p3*r**2)/12
SAMPLE_ONLY | payload compiler monomial composition envelope | no counterexample in 0<=A,D<=5, 0<=p,q<=4, 1<=E<=4, 0<=n<=7
SAMPLE_ONLY | graft sum envelope | no counterexample in 0<=A,D,C<=7, 0<=p,q<=4, 0<=n<=9
SAMPLE_ONLY | bit_length(rho_d(n)) <= 1+d*n*bit_length(n+1) | no counterexample in 1<=d<=8, 0<=n<=50
SAMPLE_ONLY | for n>=1 the sharper bit_length(rho)<=d*n*bit_length(n+1) | no counterexample in 1<=d<=8, 1<=n<=50
EXPECTED_COUNTEREXAMPLE | the sharper bit-length bound fails at exponent zero | (1, 0)
SAMPLE_ONLY | sentinel packing: size(code)=payloadLength+1 and payloadLength=len(bits) | no counterexample in all bit strings of length <=10
SAMPLE_ONLY | substitute rho bit-length upper into an affine formula-length bound | no counterexample in finite nonnegative affine coefficients and 1<=d<=5, 0<=n<=15
EXPECTED_COUNTEREXAMPLE | numeric rho is not bounded by its bit length (forbidden reversed direction) | (1, 2)
EXPECTED_COUNTEREXAMPLE | base>=1 is needed for monotonicity in the exponent | (0, 0, 1)
YELLOW_SCOPE | bounded searches above are pressure tests, not proofs
YELLOW_SCOPE | no CAS result here validates PA internal provability, Pudlak applicability, object/measure identity, or the Sondow-to-G_n bridge
OVERALL: PASS for exact identities; bounded claims remain SAMPLE_ONLY
```

## 6. 🟨 未求解项和 Wolfram 待运行项

1. 🟨 **Wolfram 全部运行结果待定。** 原因仅是本机无 Wolfram Engine，而不是脚本
   返回失败。脚本中的 `FullSimplify/Refine`、`Reduce/Resolve`、有限盒
   `FindInstance[Not[claim],...,Integers]` 都必须在装有 Engine 的环境重新执行。
2. 🟨 **SymPy 无界 `rho` 单调性表达式未求解：**
   `(n+1)^(dn) < (n+2)^(d(n+1))`。这是变量整数指数命题，不属于 SymPy 的完整
   实闭域不等式过程；第 3.1 节给出了纸面证明，有限搜索只作压力测试。
3. 🟨 **SymPy 符号 ceiling 表达式未求解：** `a*ceiling(c/a)>=c`。第 3.1 节从
   `ceil` 定义给出纸面证明；`1<=a,c<=30` 的搜索不是证明。
4. 🟨 **变量指数复合包络只作有限搜索。** 一般证明使用 `n+1>=1` 下的指数单调性，
   已在第 3.4 节写出；不能把 `SAMPLE_ONLY` 解释为全称证明。
5. 🟨 **FindEquationalProof 待运行。** Wolfram 脚本只把它用于无解释乘法符号的
   交换律局部等式 `times(d,n)=times(n,d)`；若成功，完整 `ProofObject` 会打印到
   标准输出并保存为
   `/tmp/foundational_mathematical_validity_rho_exponent_proof.wl`。它不用于不等式、
   指数单调性或任何逻辑桥。

## 7. 明确不能由这些脚本验证的核心步骤

无论 Wolfram 或 SymPy 返回多少个 `True`，它们都不能验证：

- `P_direct` 的 PA 内部可证性及其证明载荷界；
- Pudlak 1986 Theorem 3.1 的原文假设是否逐项适用于当前谓词；
- proof system、checker、formula code 与 length measure 是否为同一对象；
- Sondow number-theoretic certificate 是否逻辑蕴含同一
  `G_n = not P_direct(rho_d(n),falsumCode)`；
- 对撞结论或 Euler--Mascheroni 常数的无理性。

这里的计算证据只能作为纸面算术证明的第二实现和有限反例压力测试，不能填补上述
任何逻辑缺口。
