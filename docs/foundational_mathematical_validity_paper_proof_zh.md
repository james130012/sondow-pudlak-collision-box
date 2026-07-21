# Sondow--Pudlák 对撞路线的基础数学有效性判决

## 摘要

本文从实际公开检查器所接受的对象出发，审查以有限一致性句族连接 Pudlák 下界与
Sondow 判据的论证。审查得到三个结论。第一，当前二元公式确实在标准模型中精确表达
“存在一份完整 proof tree 与 structural certificate，其完整载荷不超过给定界且公开
检查器接受”。第二，**若**对这个精确公式、这个证明系统和这个完整载荷度量建立
Pudlák 1986 定理 3.1 的全部内部推导条件，则完美幂重标定
$\rho_d(n)=(n+1)^{dn}$ 的算术步骤正确，并给出最终下界
$(n+1)^n<M(n)$。但是这些推导条件目前没有建立；已有的外部接受性编译器既不是
条件 (2)、(3) 所需的 PA 内部蕴含证明，也没有完整载荷的统一多项式界。第三，Sondow
原定理从 $\gamma\in\mathbb Q$ 给出的是一个关于 $S_n,I_n,d_{2n}$ 的实数/整数关系，
并不给出同一句 $G_n$ 的 PA 证明。故当前材料不能推出目标碰撞。

按交接单规定的四分法，最终判决是 **C：Pudlák 下界的文献条件或对象校准未成立**。
此外，Sondow 到同一 $G_n$ 的上界桥也是独立的红色缺口。本文不给这些缺口添加公设。

## 1. 数学对象

### 1.1 理论与推导

令 $A=\mathrm{PA}$ 为仓库中 `LO.FirstOrder.Arithmetic.Peano` 所表示的经典一阶
Peano 算术。它的非逻辑公理包括等词公理、加乘与序公理，以及对任意一元算术公式的
归纳公理。当前公开检查器检查的不是一列 Hilbert 公式，而是一个**单边有限集序列演算**
的树状推导。以 $\Gamma,\Delta$ 表示有限公式集，其规则逐项为：

$$
\begin{array}{ll}
\mathrm{closed}:&\varphi,\neg\varphi\in\Gamma\Rightarrow A\Rightarrow\Gamma;\\
\mathrm{axm}:&\sigma\in A,\ \sigma\in\Gamma\Rightarrow A\Rightarrow\Gamma;\\
\mathrm{verum}:&\top\in\Gamma\Rightarrow A\Rightarrow\Gamma;\\
\land:&\varphi\land\psi\in\Gamma,\ A\Rightarrow\Gamma\cup\{\varphi\},
 A\Rightarrow\Gamma\cup\{\psi\}\Rightarrow A\Rightarrow\Gamma;\\
\lor:&\varphi\lor\psi\in\Gamma,\ A\Rightarrow\Gamma\cup\{\varphi,\psi\}
 \Rightarrow A\Rightarrow\Gamma;\\
\forall:&\forall x\,\varphi\in\Gamma,\ A\Rightarrow
 \operatorname{shift}(\Gamma)\cup\{\operatorname{free}(\varphi)\}
 \Rightarrow A\Rightarrow\Gamma;\\
\exists:&\exists x\,\varphi\in\Gamma,\ A\Rightarrow\Gamma\cup\{\varphi[t/x]\}
 \Rightarrow A\Rightarrow\Gamma;\\
\mathrm{wk}:&A\Rightarrow\Delta,\ \Delta\subseteq\Gamma\Rightarrow A\Rightarrow\Gamma;\\
\mathrm{shift}:&A\Rightarrow\Gamma\Rightarrow A\Rightarrow\operatorname{shift}(\Gamma);\\
\mathrm{cut}:&A\Rightarrow\Gamma\cup\{\varphi\},\
 A\Rightarrow\Gamma\cup\{\neg\varphi\}\Rightarrow A\Rightarrow\Gamma.
\end{array}
$$

PA 公理的公开证书构造子逐项为 `eqRefl`、`eqSymm`、`eqTrans`、`eqFuncExt`、
`eqRelExt`、`addZero`、`addAssoc`、`addComm`、`addEqOfLt`、`zeroLe`、
`zeroLtOne`、`oneLeOfZeroLt`、`addLtAdd`、`mulZero`、`mulOne`、`mulAssoc`、
`mulComm`、`mulLtMul`、`distr`、`ltIrrefl`、`ltTrans`、`ltTri` 和
`induction(body)`。结论为单元素有限集 $\{\varphi\}$ 时，称该树证明
$\varphi$。这个演算与 Foundation 的 `Derivation2 PA {φ}` 对应。

因此，除非另给证明系统模拟及长度校准定理，本文不会把当前对象称作 Buss 论文中的
Hilbert proof。逻辑上的可相互模拟不等于完整编码长度已经按所需方向多项式校准。

### 1.2 证明对象、证书与公开检查器

一份公开证明码解码为二元组

$$
  (T,C),
$$

其中 $T$ 是 `ListedCheckedPAProofTree`，$C$ 是
`StructuralValidityCertificate`。树节点保留每个序列的公式列表以及规则所需的公式、
项和子树。证书的形状为叶、PA 公理证书、一元证书或二元证书；PA 公理证书逐项指明
等词、加乘、序或归纳公理。局部检查同时核对：

1. 树与证书可从整个 proof payload 唯一解析且没有剩余后缀；
2. 每个节点满足对应序列规则，公理节点带合法的 PA 公理证书；
3. 根结论的有限集等于 $\{\varphi\}$；
4. $\varphi$ 的紧凑公式码等于公开输入 $y$。

记这个布尔程序为

$$
  V(c,y)\in\{\mathsf{false},\mathsf{true}\}.
$$

`compactNumericListedPublicVerifier` 与列表版 certified verifier 已有逐点相等定理，
而后者接受时可投影为真实的 `Derivation2 PA {φ}`。这里的 checker soundness 是关于
当前序列演算的，不是关于另一个 root-level `proof_length` 函数的约定。

### 1.3 完整载荷长度

自然数码 $c$ 的二进制表示末端含一个值为 $1$ 的 sentinel。定义

$$
  L(c):=\operatorname{packedPayloadLength}(c)
       :=\operatorname{Nat.size}(c)-1.
$$

对规范打包的位串，$L(c)$ 恰为 sentinel 之前的位数。proof tree tokens 与
structural-certificate tokens 先连接，再编码为这一条 payload；故 $L$ 计量的是完整
`proof + certificate`，不是仅树节点数、仅 proof-code 数值、仅 `Nat.size`，也不是
另一个系统中的 symbol count。公开的公式码输入本身不另加到 $L(c)$，但根公式及各
节点公式已经编码在树中。

### 1.4 有限一致性句族

令 $\botCode$ 是算术假式在当前 `compactFormulaCode` 下的码。定义

$$
\begin{aligned}
 P_{\rm dir}(b,y)
   &:\Longleftrightarrow
      \exists c\,[L(c)\le b\ \land\ V(c,y)=\mathsf{true}],\\
 F_b&:=\neg P_{\rm dir}(b,\botCode),\\
 R(n)&:=(n+1)^n,\\
 \rho_d(n)&:=(n+1)^{dn}=R(n)^d,\\
 G_{d,n}&:=F_{\rho_d(n)}.
\end{aligned}
$$

当 $d$ 固定后，简写 $G_n=G_{d,n}$。令

$$
 M_d(n):=\min\{L(c):V(c,\ulcorner G_{d,n}\urcorner)=\mathsf{true}\}.
$$

若集合为空，暂取 $M_d(n)=+\infty$。这避免把“每个标准有限一致性实例可证”这一
尚未接到当前定量端点的事实偷偷放入定义。任何目标上界都会同时证明该集合非空。
仓库中的 `minListedCertifiedPAProofPayloadLength` 对空集返回 $0$，所以把它与这里的
$M_d$ 等同还需要一个该实例确有当前 checker 可接受证明的端点。

### 1.5 参数、数词和“固定多项式”

$b,n,d,q$ 在元理论里是自然数值，且有理表示的分母 $q>0$；一般把分子
$p$ 取为整数（对正的 $\gamma$ 可取正整数）。写进 PA 公式时，$b$ 与公式码用
短二进制闭项表示；它们不是一元数词。固定 $d$ 时

$$
 \log_2\rho_d(n)=dn\log_2(n+1),
$$

所以 $\rho_d(n)$ 的**数值**关于外层 $n$ 超多项式，而其二进制数词长度为
$O(dn\log(n+1))$，关于 $n$ 是多项式有界的。这两个量不能互换。

所谓固定多项式 $U(n)$，其次数和系数均不得依赖 $n$。在假设
$\gamma=p/q$ 的上界中，它们可以依赖已经固定的 $p,q,d$、理论、编码和编译器；
这一依赖必须在量词顺序中位于 $\forall n$ 之前。

### 1.6 一致性的使用位置

元理论中的 $\operatorname{Con}(\mathrm{PA})$ 有两处合法用途：

* 从 checker soundness 排除一个被接受的 $\bot$ 推导，得到每个标准 $F_b$ 为真；
* 满足 Pudlák 定理对理论 $A$ 的一致性假设。

它不能被当作 PA 内部的一条可自由使用的公理来构造 $G_n$ 的短证明。当前
`models_compactListedPADirectFiniteConsistencySentence` 是标准模型真值结论，不是
`CertifiedPAProof G_n`，尤其不是一个带多项式 payload 界的证明族。

## 2. 当前直接谓词的精确性

**引理 2.1（标准模型精确性）。** 对所有标准自然数 $b,y$，当前二元
$\Sigma_1$ 公式的求值满足

$$
 \mathbb N\models P_{\rm dir}(\bar b,\bar y)
 \quad\Longleftrightarrow\quad
 \exists c\,[L(c)\le b\land V(c,y)=\mathsf{true}].
$$

**证明。** `CompactNumericListedDirectPredicateMatrix` 的见证包含 proof code、规范输入
tableau、拆分位置、完整接受 trace、公式 token tableau 和唯一根结论行。正向精确性
从这些见证恢复整个公开输入及 checker 接受；反向精确性从任一满足长度界的被接受码
构造规范 tableau。公式层定理由
`compactListedPADirectProofFormula_iff_exists_publicVerifier` 给出。长度坐标在两侧都是
同一个 `packedPayloadLength`，公式码在两侧都是公开输入 $y$。∎

**引理 2.2（外部单调性）。** 若 $b\le b'$ 且
$P_{\rm dir}(b,y)$，则 $P_{\rm dir}(b',y)$。

**证明。** 保留同一个 $c$，由 $L(c)\le b\le b'$ 即得。∎

这个引理是元理论中的语义命题。Pudlák 条件 (0) 要求的是理论 $A$ 内部对其选定公式
的证明；两者不能混为一谈。

## 3. Pudlák 1986 定理及其适用性

### 3.1 一手文献中的定理

Pavel Pudlák, *On the length of proofs of finitistic consistency statements in first
order theories*, in *Logic Colloquium '84*, Studies in Logic and the Foundations of
Mathematics 120, North-Holland, 1986, pp. 165--196；定理 3.1 在印刷页 172。
[作者 PDF](https://users.math.cas.cz/~pudlak/fin-con.pdf)，
[出版记录与 DOI](https://doi.org/10.1016/S0049-237X(08)70462-2)。

论文把公式与证明编码成二字母串，令 $|t|$ 表示串长；
$A\vdash^r\varphi$ 计的是整份 proof 中至多 $r$ 个符号，包含其中出现的公式，
不是仅计算 proof 行数或最终公式长度。其编码背景还要求代入等语法运算有高效编码，
并能在 $Q$ 中以多项式长度证明所需的编码等式。定理 3.1 的实质假设是：
$A\supseteq Q$ 一致，且存在公式 $P(x,y)$ 和多项式
$p_1,p_2,p_3,q_1,q_2$，使下列有限版推导条件成立：

$$
\begin{array}{ll}
(0)& A\text{ 内部证明 proof-bound 的单调性};\\[2mm]
(1)& A\vdash^{n}\varphi\Longrightarrow
      A\vdash^{p_1(n)}P(\bar n,\ulcorner\varphi\urcorner);\\[2mm]
(2)& A\vdash^{p_2(|n|,|m|)}
      \bigl(P(\bar n,\bar m)\to
      P(\overline{q_1(n)},
        \ulcorner P(\bar n,\bar m)\urcorner)\bigr);\\[2mm]
(3)& A\vdash^{p_3(|n|,|\varphi|,|\psi|)}
      \bigl(P(\bar n,\ulcorner\varphi\urcorner)\land
      P(\bar n,\ulcorner\varphi\to\psi\urcorner)
      \to P(\overline{q_2(n)},\ulcorner\psi\urcorner)\bigr).
\end{array}
$$

其印刷结论是存在 $\varepsilon>0$，使**不存在任何** $n\in\omega$ 令 $A$ 有
长度至多 $n^\varepsilon$ 的 proof 证明
$\neg P(\bar n,\ulcorner\bot\urcorner)$。证明主体先在充分大的参数上推导，末句再称
结论由一个初等计算和条件 (0) 得到。本文下文只使用原结论所蕴含的最终版本。原文在
定理后明确说明，它没有在那里构造
某一个特定的“自然算术化”，而是再给出足以导出这些条件的一般性质；因此定理编号本身
不能替代当前自定义谓词的实例化证明。

印刷页 172 的条件 (0) 字面确实呈现为
$x\le x'\land P(x',y)\to P(x,y)$，与紧邻文字所定义的“长度至多 $x$”以及页 177
的 Proposition 3.4 不相容；自然证明谓词所需且在后续证明中可用的是向上单调形式
$x\le x'\land P(x,y)\to P(x',y)$（或等价的变量换名）。本文如实记录这个版面问题，
对作者页面、题名加 erratum 以及定理条件的检索没有找到正式勘误。因此，严格应用时
不能静默改写：必须把更正方向列作明确版本，并由原证明重证该更正版元定理或提供权威
勘误。下文采用唯一与有限证明谓词相容的向上方向来审查项目义务；无论采用哪种读法，
当前直接公式的 PA 内部版本都仍须单独证明。

### 3.2 对当前 $P_{\rm dir}$ 的逐项审查

**条件 (0)：尚未实例化。** 引理 2.2 给出正确的外部单调性；当前材料没有给出 PA
对精确二元公式的闭合内部单调性证明。这个义务预计是常规的，但“预计可证”不是已证。

**条件 (1)：尚未定量闭合。** 当前有真实的 PA proof constructors 及若干局部 payload
界，也有 `compileAcceptedDirect`：给定一个外部具体码 $c$、外部证明
$L(c)\le b$ 和外部等式 $V(c,y)=\mathsf{true}$，它可产生闭实例
$P_{\rm dir}(\bar b,\bar y)$ 的 `CertifiedPAProof`。但这里没有一个定理给出该输出的
完整 payload 关于输入证明长度的固定多项式界；该定义还通过标准模型真值编译器工作。
所以不能据此写出 Pudlák 所需的 $p_1$。此外，还需明确把任意当前 PA proof 的完整
码转换为这个具体见证，并计量树、证书、公式码与短数词的全部成本。

**条件 (2)：当前尚未建立。** `compileAcceptedDirect` 接收的是元理论中已经选定的真见证；
条件 (2) 要求 PA 内部证明一个以 $P(\bar n,\bar m)$ 为前件的统一蕴含。其证明必须
在 PA 内从存在量词见证模拟 checker，再构造“这份接受事实本身有短证明”的编码，并
给出只依赖 $|n|,|m|$ 的 $p_2$ 及固定 $q_1$。当前没有这样的定理。外部
checker 可运行、谓词是 $\Sigma_1$、或某个真闭实例可编译，都不蕴含这一内部反射。

**条件 (3)：当前尚未建立。** 条件 (3) 要求在同一直接谓词内部从两份被编码证明构造
modus ponens/cut 后的证明，重建合法 structural certificate，并证明完整打包载荷不
超过固定 $q_2(n)$；还要在 PA 内证明这个变换正确且把整条蕴含的证明长度界写成
$p_3(|n|,|\varphi|,|\psi|)$。局部 MP constructor 及局部加法界并不是这个带存在
见证、解析器、checker trace 和公式码的闭合内部定理。当前没有后者。

**编码校准：当前尚未建立。** 原定理把公式与证明当作二字母串并以串长计量。当前长度是
完整 proof-tree-plus-certificate sentinel payload。要应用定理，必须选择一种方式：

* 直接以当前 payload 为 Pudlák 的 proof string，并对它重做 (0)--(3)；或
* 从文献所用 proof string 到当前树、证书和 payload 给出所需方向的显式多项式模拟。

现有的语义 exactness 不提供这种 proof-system/length-measure 校准。故不能从文献定理
直接得出当前 $M_d$ 的固定正幂下界。

### 3.3 条件下的完美幂重标定

下面把纯算术部分完整证明，以区分“算术正确”和“定理前提缺失”。

**引理 3.1（条件下界）。** 假设对当前精确对象已经证明：存在
$\varepsilon>0$ 与 $B_0\in\mathbb N$，对每个 $b\ge B_0$，

$$
 M_F(b)>b^\varepsilon,
$$

其中 $M_F(b)$ 是同一 checker、同一 payload 下 $F_b$ 的最短证明长度。则存在固定
$d\ge1$ 和显式阈值 $N_0$，使 $n\ge N_0$ 时

$$
 (n+1)^n<M_d(n).
$$

**证明。** 取正有理数 $a/c\le\varepsilon$，其中 $a,c\ge1$，并令

$$
 d=\left\lceil\frac ca\right\rceil,
 \qquad N_0=\max\{1,B_0\}.
$$

于是 $ad\ge c$。对 $n\ge N_0$，有 $\rho_d(n)\ge B_0$ 且底数
$n+1>0$。记 $R=(n+1)^n$。自然数幂律给出

$$
 \rho_d(n)^a
   =(n+1)^{adn}
   \ge(n+1)^{cn}
   =R^c.
$$

在正实数中取正 $c$ 次根，得到
$\rho_d(n)^{a/c}\ge R$。又因 $\rho_d(n)\ge1$ 且
$\varepsilon\ge a/c$，

$$
 M_d(n)=M_F(\rho_d(n))
   >\rho_d(n)^\varepsilon
   \ge\rho_d(n)^{a/c}
   \ge R=(n+1)^n.
$$

所有不等式方向及最后的严格性均已保留。∎

**注。** 固定 $d$ 后，写入 $G_{d,n}$ 的 cutoff 数词只需
$O(dn\log(n+1))$ 位。故重标定没有把二进制数词成本隐藏为 $\rho_d(n)$ 的裸数值。
反过来，这个短数词事实也不能补出 Pudlák 的内部推导条件。

**引理 3.2（载体最终超过固定多项式）。** 若实值函数 $U$ 满足
$U(n)\le c(n+1)^k$，其中 $c\ge0$、$k\in\mathbb N$ 固定，则
$U(n)<(n+1)^n$ 最终成立。

**证明。** 取整数 $C\ge c$。若 $n\ge C+k+1$，令 $B=n+1$，则
$C<B$、$B^k>0$ 且 $k+1\le n$。因此

$$
 U(n)\le cB^k\le CB^k<B^{k+1}\le B^n=(n+1)^n.
$$

任意固定实系数多项式的绝对值都可被这种 $c(n+1)^k$ 支配，故结论覆盖通常的
fixed-polynomial upper。∎

**推论 3.3（条件碰撞）。** 若引理 3.1 的 exact lower 和缺失定理 U 的 exact upper
同时成立，则 $\gamma=p/q$ 导致矛盾。

**证明。** U 给出被同一 checker 接受的 $G_{d,n}$ proof，故
$M_d(n)\le U(n)$。引理 3.2 最终给出
$U(n)<R(n)$，而引理 3.1 给出 $R(n)<M_d(n)$，于是
$M_d(n)\le U(n)<R(n)<M_d(n)$，矛盾。∎

## 4. Buss 1994 定理 5 的范围

Samuel R. Buss, *On Gödel's theorems on lengths of proofs I: Number of lines and
speedup for arithmetics*, *Journal of Symbolic Logic* 59(3), 1994, pp. 737--756；
定理 5 的正式期刊版陈述始于印刷页 742，证明在页 743；该证明在论文中以梗概形式给出。
[作者 PDF](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/godelone/paper.pdf)，
[出版记录与 DOI](https://doi.org/10.2307/2275906)。

该节固定一致、可公理化、含 $+$ 与 $\cdot$ 的算术理论 $T$，要求它能有效算术化
元数学（例如扩定义后包含 $S^1_2$ 或 $I\Delta_0+\Omega_1$），并固定多项式时间可
识别的公理化、短二进制项以及 Hilbert-style symbol length。对 time-constructible
$f$，定理 5 给出与 $f$ 无关的常数 $\varepsilon>0,c\in\mathbb N$，使充分大
的 $n$ 上不存在不超过 $f(n)^\varepsilon$ symbols 的 $T$-proof 证明
$\operatorname{Con}_T((f(n))^c)$。其中公式按 time constructor
$g(x)=f(x)^c$ 解释；若偏函数 $f(n)$ 未定义，论文另说明相应一致性实例根本不可证。

这是一条推广性的重标定下界，不是当前主路线的必要输入：一旦引理 3.1 的前提由
Pudlák 对当前 $P_{\rm dir}$ 真正实例化，完美幂算术已经完成目标。反之，Buss 定理
不能绕过对象校准，因为它的 Hilbert proof、symbol length 与
$\operatorname{Con}_T$ 尚未证明等于当前树、证书、checker、payload 和 $F_b$。

## 5. Sondow 判据实际给出的结论

Jonathan Sondow, *Criteria for Irrationality of Euler's Constant*,
*Proceedings of the American Mathematical Society* 131(11), 2003,
pp. 3335--3344；定理 4、5 的陈述均在印刷页 3340，定理 5 的一行证明续至 p. 3341。
[AMS 版本](https://www.ams.org/journals/proc/2003-131-11/S0002-9939-03-07081-3/S0002-9939-03-07081-3.pdf)，
[arXiv 原稿](https://arxiv.org/abs/math/0209070)，
[DOI](https://doi.org/10.1090/S0002-9939-03-07081-3)。

令 $d_m=\operatorname{lcm}(1,\ldots,m)$，并定义

$$
 I_n=\int_0^1\!\int_0^1
 -\frac{(x(1-x)y(1-y))^n}{(1-xy)\log(xy)}\,dx\,dy
$$

及显式正整数

$$
 S_n=\prod_{k=1}^n
     \prod_{i=0}^{\min(k-1,n-k)}
     \prod_{j=i+1}^{n-i}
       (n+k)^{(2d_{2n}/j)\binom ni^2}.
$$

论文证明

$$
 \log S_n-d_{2n}I_n
 =d_{2n}A_n-d_{2n}\binom{2n}{n}\gamma,
 \qquad d_{2n}A_n\in\mathbb Z.
$$

论文的 Lemma 3 还给出（$n\ge1$）
$1<d_{2n}<8^n$ 与 $0<I_n<16^{-n}$，故
$0<d_{2n}I_n<1$。定理 4 因而说：固定 $n$ 时，
$\{\log S_n\}=d_{2n}I_n$ 当且仅当
$\gamma=p/q$ 对某些既约整数 $p,q$（$q>0$）成立，且
$q\mid d_{2n}\binom{2n}{n}$。定理 5 说该等式对某个 $n$ 成立、对所有充分大
$n$ 成立、以及 $\gamma$ 有理，三者等价；方向
$\gamma=p/q\Rightarrow$ 最终成立使用了 $n\ge\lceil q/2\rceil$ 时
$q\mid d_{2n}$。在这个尾部可明确写出整数

$$
 z_n=d_{2n}A_n-\frac{d_{2n}}q\binom{2n}{n}p,
$$

于是 $\log S_n-d_{2n}I_n=z_n$。这里“$\gamma=p/q$”本身仍是外部解析假设；
整数证书只能核对由固定 $p,q,n$ 形成的有限等式，不能由 checker 验证实常数
$\gamma$ 与该有理数相等。

这就是文献提供的全部相关信息：一个明确的实积分、整数积、整除性和小于 1 的正余项
所形成的分数部等式。文献没有定义当前 PA checker、$P_{\rm dir}$、$F_b$ 或
$G_{d,n}$，也没有声称由该等式可构造这些句子的短 PA proof。

## 6. Sondow 上界桥的严格缺口

设 $C_{p,q,n}$ 表示把 Sondow 的上述整数/实数关系形式化后得到的证书句。即使已经
额外证明 $C_{p,q,n}$ 可由多项式时间 checker 检查，最多先得到“该计算可在某个理论
中被短证明”的另一条编译义务。它的结论公式仍是 $C_{p,q,n}$，不是

$$
 G_{d,n}=\neg P_{\rm dir}
   (\overline{(n+1)^{dn}},\overline{\botCode}).
$$

要得到目标上界，至少必须证明下列**同对象上界定理**。

**缺失定理 U（精确形式）。** 对固定 $d\ge1$ 和固定有理性见证
$p\in\mathbb Z,q\in\mathbb N_{>0}$，存在 $N,C,k$ 及统一可计算函数
$\operatorname{build}_{p,q,d}:\mathbb N\to\mathbb N$，使
$\gamma=p/q$ 时，对每个 $n\ge N$，

$$
\begin{aligned}
 V(&\operatorname{build}_{p,q,d}(n),
     \operatorname{compactFormulaCode}(G_{d,n}))
     &=\mathsf{true},\\
 L(&\operatorname{build}_{p,q,d}(n))&\le C(n+1)^k.
\end{aligned}
$$

并且 `build` 的正确性只能使用 $p/q$ 与 Sondow 关系的已验证形式化；除目标句的
公开语法外，不得把 $G_{d,n}$ 的真值或已有证明、有限一致性、Pudlák 下界或最终
无理性结论作为输入字段。

也可把 U 分解成两项：先构造 $C_{p,q,n}$ 的当前 certified PA proof，再构造一族
当前 certified PA proofs 证明

$$
 C_{p,q,n}\longrightarrow G_{d,n},
$$

并对两者的完整 payload 给出固定多项式界。第二项正是缺少的信息流：Sondow 关系只谈
特定整数和实数，为什么它会排除**所有**长度不超过 $\rho_d(n)$ 的 PA 矛盾证明？
现有前提没有回答这个问题。

**引理 6.1（公式错位不能推出碰撞）。** 从
$C_{p,q,n}$ 有短证明和 $G_{d,n}$ 无短证明，若没有
$C_{p,q,n}\to G_{d,n}$ 的定量证明或直接 `build`，不能推出矛盾。

**证明。** 在抽象 proof-length 赋值中令
$\ell(C_{p,q,n})=1$，令
$\ell(G_{d,n})=(n+1)^n+1$。这同时满足“$C$ 多项式短”和“$G$ 超过载体”，
却不满足 $G$ 的多项式上界，也没有矛盾。故从源公式的短证性到目标公式的短证性
必须有额外推理规则；仅给两个名字或两个码函数不能完成该推理。∎

替换测试得到同一结论：若“任意有短可检验证书的命题”都可无条件产生当前有限一致性
的短证明，则可把 Sondow 证书换成诸如 $2+2=4$ 的短证书；这会直接与一旦建立的
Pudlák 下界冲突。因此这种通用原则过强，不能被“可检查所以 PA 中短可证”代替。

缺失定理 U 若与本路线所需的 Pudlák 下界同时严格建立，就会完成对撞并证明
$\gamma$ 无理。鉴于该无理性仍是未解决问题，不能把 U 当作可从 Sondow 论文摘录
出的常规编译细节；**U 与 exact lower 的组合**将构成新数学突破。这里既没有证明 U，
也没有证明 U 不可能；证明的是现有前提与文献不蕴含 U。

## 7. 主定理与判决

**主定理（当前材料的有效性判决）。** 对第 1 节固定的当前直接谓词、当前序列演算、
当前公开 checker 和完整 proof-plus-certificate payload：

1. $P_{\rm dir}$ 的标准模型精确性成立；
2. Pudlák 固定正幂下界一旦对这个精确对象建立，引理 3.1 的重标定严格给出
   $(n+1)^n<M_d(n)$；
3. 当前材料没有建立 Pudlák 条件 (0)--(3) 所需的全部 PA 内部定量定理，特别是
   (2)、(3)，也没有完成文献 proof-string 与当前完整 payload 的校准；
4. Sondow 的一手定理只给出第 5 节的 number-theoretic relation，没有给出缺失定理 U；
5. 因此当前不能证明目标下界，也不能证明同一 $G_n$ 的 Sondow 多项式上界，更不能
   推出碰撞。

**证明。** 第 1 项为引理 2.1；第 2 项为引理 3.1；第 3 项由第 3.2 节逐项比较定理的
量词与现有端点得到；第 4 项由 Sondow 定理 4、5 的精确结论和第 6 节的公式比较得到；
第 5 项由第 3、4 项及引理 6.1 立即得到。∎

所以四选一的最终判决为：

> **C. Pudlák 下界的文献条件或对象校准未成立。**

这个选择不表示 Sondow 上界已经成立；相反，上界的同对象桥也为红色缺口。之所以不选
B，是因为 B 要求下界已经成立；不选 D，是因为没有发现当前精确定义本身的反例或逻辑
矛盾，发现的是两个未证明且不可由所引文献自动补出的必要定理。
