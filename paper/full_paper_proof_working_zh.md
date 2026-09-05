# Sondow–Pudlak 路线：统一纸面证明工作稿

日期：2026-09-05。先完成整条纸面证明，再进行形式化。

本文集中写出实际数学构造及证明。第 3 节给出不查询实数相等的有限有理数证书；
第 4 节证明其位复杂度；第 5 节消除一类树状证明复制障碍。
这些结果尚未构成 Euler 常数无理性证明：第 7 节所列的同对象归约仍未证明，
当前直接证明谓词的单调性与高效固定点已在第 6.1a–6.1b 节纸面闭合；
条件 (1)、(2)、(3) 仍须具体建立。
“工作稿”不表示这些未证条件可以在最后的对撞中省略。

## 整体逻辑判定

条件性对撞规则本身正确：如果同一 PA 系统、同一公式 G_n、同一完整载荷度量下，
既有最终超多项式下界，又能在有理性假设下独立构造多项式上界，则有理性假设导致矛盾。
目前不成立的是把这些独立条件视为已经由 Sondow 判据和通用编译器一并提供。

框架中已定位的实质问题如下：

- Sondow 数论证书和 PA 有限一致性句是不同对象；前者有短证明不能直接传递给后者。
- 对语法检查的可靠性作元理论证明，并不提供 PA 内部的反射实例；第 7.2 节精确定位此处。
- 原路线曾混用未重标定 F_n 与 G_n，以及旁支长度和当前完整载荷；本稿已固定共同对象。
- 原 Prop 接受定义直接含有理参数等于 gamma，不能计作有限布尔检查；第 3 节提供替代构造。

这些问题不足以证明所有可能的归约都不存在，也不否定已独立成立的数论恒等式和局部编译器。
但它们足以说明，现有整体路线还不是一份无条件无理性证明。
其中对象记号和接受接口可修正；从特定数论内容到 G_n 的短推导必须由新的数学论证补出。

进一步的独立复核没有发现第 6 节条件推导另有致命错误：普通句法一致性足以完成
固定点的反证；条件 (1) 使用真实短证明长度；条件 (2)、(3) 区分内部长度界与
外部证明的位复杂度；固定多项式与共同尾部参数的量词次序一致。
这项复核只覆盖已写出的条件推导，不替代当前 P_direct 的前提实例化。

全局依赖图也必须据此阅读：M16 的有限检查器是本稿替代构造，未成为旧 Prop 接口的
新形式化实现；M17 是独立未证的数学归约，不能再标为“等待通用编译器即可接上”；
M11 的新增形式化按用户要求暂停。下界首先采用“无短证明”，最小值写法须另有可证性。

## 1. 唯一的最终目标

固定当前 PA 系统、公开证明检查器 V、完整证明树加结构证书的载荷长度 L。
令 P(b,f) 表示存在 V 接受、结论码为 f、且 L 不超过 b 的证明码。
令 F_b = NOT P(b,falsumCode)。固定正整数 d，定义

```text
rho_d(n) = (n+1)^(d*n)
G_n = F_{rho_d(n)}
M(n) = 同一检查器与同一载荷度量下 G_n 的最短证明长度。
```

最短长度记号只在存在证明时使用。严格的下界陈述是“没有长度不超过指定界的证明”。
当前 Lean 的 `minListedCertifiedPAProofPayloadLength` 在不存在证明时返回 0，
因此不能把“无短证明”未经可证性论证就改写成该 Nat 函数的大于式。
最终上界 U 若成立会同时给出可证性，此时两种表述可以用于同一实例的对撞。

需要先独立完成下界 D：M(n) 最终超过任何关于外层 n 的固定多项式。
再独立完成上界 U：对固定整数 p、正整数 q，若 gamma=p/q，
则 G_n 最终有完整载荷不超过 C*(n+1)^k 的真实 PA 证明，其中 C、k 固定。
二者成立才可取共同尾部参数得到矛盾。

这里 p/q 是显式有理数；下文 q 一律表示正整数分母。
旧 Lean 文件的变量名 q 有时表示整个有理数，不能混读。

## 2. 数论起点与精确残差

对 n≥1，令 D_n=lcm(1,…,2n)，B_n=binom(2n,n)，
A_n=sum(i=0,…,n) binom(n,i)^2 H_(n+i)，T_n=D_n A_n。
T_n 是整数：展开每个 H_(n+i) 后，其分母均整除 D_n。

S_n 为 Sondow 的正整数幂积：

```text
S_n = product(k=1,…,n)
        product(i=0,…,min(k−1,n−k))
          product(j=i+1,…,n−i)
            (n+k)^[(2D_n/j)*binom(n,i)^2]。
```

Sondow 的解析恒等式与积分界给出

```text
I_n = B_n*gamma + log(S_n)/D_n − A_n
0 < I_n < 16^(−n)，D_n < 8^n。
```

这里 log 是自然对数。积分 I_n 的被积函数为
`[x(1−x)y(1−y)]^n / [−(1−xy)log(xy)]`，在单位正方形内取二重积分。
上述定义、恒等式和界来自 Sondow 原文公式 (2)、(3)、(5)、(6) 及 Lemma 3。
本工作稿在这些已发表数论结果上继续推导；不是声称重新证明了该论文的解析部分。
来源：[Sondow 原文](https://arxiv.org/pdf/math/0209070)。

给定整数 p 和正整数 q，设 Z_n=qT_n−D_n B_n p，并设

```text
Y_n(p/q) = log(S_n) − Z_n/q。
```

由恒等式直接移项得到

```text
Y_n(p/q) = D_n I_n + D_n B_n*(p/q−gamma)。       (2.1)
```

注意误差项的符号：p/q 大于 gamma 时它为正。式 (2.1) 对任意 p/q 成立，
不预先使用有理性。Z_n 是有符号整数，不能强制使用自然数减法截断。

因此精确等式 Y_n(p/q)=D_n I_n 与 gamma=p/q 等价。
把这条实数等式作为“检查通过”的字段，会把原假设再次放进检查器。
下面改为只接受有理数运算轨迹和有理数不等式。

## 3. 有限有理证书的构造与完备性

### 3.1 为正余项建立显式下界

在小正方形 [1/4,1/2]×[1/4,1/2] 上，
x(1−x)、y(1−y) 均不小于 3/16；xy≥1/16，故
`−(1−xy)log(xy) ≤ log 16 < 4`。该正方形面积为 1/16。
因此令 a_n=(9/256)^n/64，就有

```text
I_n ≥ a_n，且 a_n ≤ D_n I_n < 2^(−n)。         (3.1)
```

证明只使用积分的正性、限制积分区域与前节的上界。

### 3.2 不展开 S_n，计算 log(S_n) 的有理区间

将相同底数的指数合并为非负整数 e_(n,k)，于是
`log(S_n)=sum(k=1,…,n) e_(n,k)*log(n+k)`。
原幂积至多有 n^3 项，每个指数不超过 2D_n 4^n。
使用稍宽的 D_n≤9^n，可得

```text
sum(k=1,…,n) e_(n,k) ≤ 2(n+1)^3 36^n。        (3.2)
```

取整数 t=8(n+1)^2。对整数 v=n+k，设 w=(v−1)/(v+1)，并定义有理数

```text
P_t(v) = 2*sum(j=0,…,t−1) w^(2j+1)/(2j+1)
R_t(v) = 2*w^(2t+1)/[(2t+1)*(1−w^2)]。
```

由 `log v = 2*sum(j≥0) w^(2j+1)/(2j+1)`，
以及尾部每个分母不小于 2t+1，逐项比较几何级数，得到

```text
P_t(v) ≤ log v ≤ P_t(v)+R_t(v)。
```

该级数可由在 [0,w] 上对几何级数 `1/(1−u^2)` 逐项积分推出；
0<w<1 保证收敛。定义

```text
L_n = sum(k=1,…,n) e_(n,k)*P_t(n+k)
U_n = L_n + sum(k=1,…,n) e_(n,k)*R_t(n+k)
Delta_n = U_n−L_n。
```

于是 L_n≤log(S_n)≤U_n，所有 L_n、U_n 的构造都是有限有理数运算。

### 3.3 统一误差证明

因为 n+k≤2n，1−w≥1/(n+1)，且 1−w^2≥1/(n+1)。
用 1−u≤exp(−u)，得到

```text
R_t(n+k) ≤ 2(n+1)*exp(−16(n+1))。
```

这里使用 2t+1≥16(n+1)^2，并将分母中的 2t+1 粗略下界为 1。
再由 (3.2)，

```text
Delta_n ≤ 4(n+1)^4 36^n exp(−16(n+1)) < a_n/4。    (3.3)
```

最后一个严格不等式可以不借助数值实验核验：左端除以 a_n/4，所得为
`1024(n+1)^4 1024^n exp(−16(n+1))`。
其自然对数小于
`7+4n+7n−16(n+1)=−5n−9<0`，因为 log 1024<7，log(n+1)≤n。
例如 log 2<7/10 可由 exp(7/10)>1+7/10+(7/10)^2/2+
(7/10)^3/6+(7/10)^4/24>2 得到，故 log 1024=10 log 2<7。

### 3.4 检查器与正向定理

定义有限检查 C(p,q,n)：按以上固定算法核对 D_n、B_n、T_n、e_(n,k)、
Z_n、L_n、U_n 的整数及有理数计算轨迹，再检查

```text
n≥1，q>0，q≤2n，
0 < qL_n−Z_n，
qU_n−Z_n < q*2^(1−n)。                         (3.4)
```

分母约定为正，所有比较通过交叉相乘化为整数比较。
验证者必须重算或逐步检查轨迹，不接受无来源的区间端点。
检查器中没有 gamma、积分值、实数相等、PA 一致性或证明长度下界。
q≤2n 仅保持与旧分母尾部一致；本区间算法不需要利用 q 整除 D_n。

**定理 3.1。** 若 gamma=p/q，则对每个 n≥max(1,ceil(q/2))，C(p,q,n) 接受。

证明：由 (2.1)，Y_n=D_n I_n。由 (3.1)、(3.3)，

```text
L_n−Z_n/q ≥ Y_n−Delta_n > 3a_n/4 > 0。
U_n−Z_n/q ≤ Y_n+Delta_n < 2^(−n)+a_n/4 < 2^(1−n)。
```

最后一步使用 a_n≤D_n I_n<2^(−n)。乘正数 q，即得 (3.4)。证毕。

### 3.5 反向定理

**定理 3.2。** 对固定整数 p、正整数 q，以下三个命题等价：

1. gamma=p/q；
2. C(p,q,n) 对所有充分大的 n 接受；
3. C(p,q,n) 对无界多个 n 接受。

证明：1 到 2 已证，2 到 3 直接成立。若某个 n 接受，由区间可靠性有
`0<Y_n<2^(1−n)`。又 `0<D_n I_n<2^(−n)`，所以 (2.1) 给出

```text
|p/q−gamma| < 2^(1−n)/(D_n B_n) ≤ 2^(1−n)。
```

若接受的 n 无界，右端可任意小；固定的非负左端只能为零。证毕。

这既没有用有限次检查证明有理性，也没有证明实际存在有理数使检查在无界多个 n 上通过。
证明的是一个显式有限证书族与有理性之间的精确关系。

### 3.6 接受判断等价于窄区间内的小分母有理数

将第 (3.4) 式的两个比较直接解出 p/q，定义有理端点

```text
alpha_n = (T_n−L_n)/(D_n B_n)
beta_n  = (T_n−U_n+2^(1−n))/(D_n B_n)
J_n = (alpha_n,beta_n)。
```

当 n≥1、q>0 时，有限检查 C(p,q,n) 接受当且仅当

```text
q≤2n，且 alpha_n < p/q < beta_n。                  (3.5)
```

规范计算日程固定且每一步可检查，因此这里没有另一个未选择的运行见证。
由第 (2.1) 式和误差界，

```text
gamma−alpha_n = (L_n−log S_n+D_n I_n)/(D_n B_n) > 0，
beta_n−gamma = (log S_n−U_n+2^(1−n)−D_n I_n)/(D_n B_n) > 0。
```

所以 J_n 无条件包含 gamma。它的宽度为

```text
(beta_n−alpha_n) = (2^(1−n)−Delta_n)/(D_n B_n)
                 < 2^(1−n)/(D_n B_n)。
```

该重新表达显示：新证书所提供的具体数论信息，是一个已证明包含 gamma 的窄有理区间，
以及区间内某个有理数的分母限制。它没有在源端使用 PA 有限一致性。

### 3.7 接受值的唯一性与相邻参数约束

先注意 B_n=product(j=1,…,n) (n+j)/j ≥ 2^n。
每个通过检查的 r=p/q 因而满足

```text
|r−gamma| < 2^(1−n)/(D_n B_n) ≤ 2*4^(−n)。          (3.6)
```

两个不同有理值 p/q、p'/q' 的距离至少为 1/(qq')，
因为 pq'−p'q 是非零整数；不需要预先假设表示已约分。

**引理 3.3。** 当 n≥4 时，第 n 层至多有一个有理值通过检查。

证明：若有两个不同通过值，由 q、q'≤2n，距离至少为 1/(4n^2)。
由 (3.6) 和三角不等式，距离严格小于 4*4^(−n)。
对 n≥4，16n^2≤4^n；n=4 时等号成立，其后可由
4(n/(n+1))^2≥1 归纳。因此两个距离界矛盾。证毕。

**引理 3.4。** 若 n≥4，第 n 层和第 n+1 层都接受某个有理值，二者必相等。

证明：若不同，两分母分别不超过 2n 和 2(n+1)，距离至少为 1/[4n(n+1)]。
另一方面，(3.6) 给出距离严格小于 (5/2)*4^(−n)。
对 n≥4，10n(n+1)≤4^n；n=4 时为 200≤256，
归纳时左侧的增长比为 (n+2)/n≤4。再次矛盾。证毕。

**定理 3.5。** gamma 有理，当且仅当每个充分大的 n 上都存在某个整数 p、正整数 q 使 C(p,q,n) 接受。

证明：有理时固定其表示，应用定理 3.1。反之取共同阈值 N≥4。
由唯一性和相邻参数约束，各层的通过有理值从 N 起均相同。
固定第 N 层的一个表示，(3.6) 随 n 趋于无穷，推出这个值等于 gamma。证毕。

所以不能通过让有理参数随每个 n 改变来绕开最终固定有理数这一要求。
但本结论使用的是所有充分大参数，不是仅仅某个稀疏无界参数集；
相邻参数引理不能擅自跨过任意长的未接受区间。

### 3.8 整层拒绝的有限证书

设 Q=2n。若能找到有理数 a/b<c/d，满足

```text
1≤b,d≤Q，bc−ad=1，b+d>Q，
a/b≤alpha_n<beta_n≤c/d，
```

则第 n 层所有分母不超过 Q 的候选均被拒绝。

证明：若 a/b<p/q<c/d，取整数 x=bp−aq、y=cq−dp，则 x、y≥1。
由 bc−ad=1，有

```text
q=d*x+b*y ≥ b+d > Q。
```

因此开区间 (a/b,c/d) 内无分母不超过 Q 的有理数，J_n 也没有。
所有展示的证书条件都是有限整数关系和有理数比较。证毕。

该模板给出一条不依赖 Pudlak 的直接数论候选：若证明这样的整层拒绝证书在无界多个 n
出现，则 gamma 不可能有任何固定分母，因为有理性会迫使之后所有层接受。
第 3.6 节的端点都可计算，单层拒绝也可穷举有限候选核实；
但“无界多个层拒绝”并没有从有限计算或上述区间宽度界中推出。
这项无界性是该候选必须另外证明的核心命题，不能作为已知输入替代第 7 节的关键桥。

### 3.9 接受或整层拒绝：完备的有限二择构造

上一节的拒绝证书不只是充分模板：给定有理数 alpha<beta 和正整数 Q，
可在关于 Q 及端点位数的多项式时间内，输出区间中的分母不超过 Q 的有理数，
或者输出上一节所需的四整数拒绝证书。

**构造与证明。** 对每个 j=1,…,Q 计算 floor(j*alpha)/j，取这些值的最大者，
约分为 a/b。于是 1≤b≤Q，a/b≤alpha，且它是所有分母不超过 Q、值不超过 alpha
的有理数中的最大者。这里 a 可以为负，floor 是向下取整，不能用自然数截断除法。

因为 gcd(a,b)=1，可以用扩展欧几里得算法取 1≤d0≤b，满足
`a*d0 = -1 mod b`。b=1 时直接取 d0=1。定义

```text
c0=(a*d0+1)/b，t=floor((Q-d0)/b)，
d=d0+t*b，c=c0+t*a。
```

d0≤b≤Q，所以 t≥0；上述数全为整数，并且

```text
1≤d≤Q，b+d>Q，b*c-a*d=1。
```

因此 c/d>a/b。由 a/b 的极大性和 d≤Q，必有 c/d>alpha。
对 a/b 与 c/d 中间任意 p/q，上一节的整数等式给 q≥b+d>Q，
故这两个端点之间不存在允许分母的有理数。

若 c/d<beta，就输出 c/d：它确实处于 (alpha,beta) 且 d≤Q。
若 beta≤c/d，就输出 (a,b,c,d)：这四数满足
`a/b≤alpha<beta≤c/d` 以及上一节全部算术条件，从而证明整层拒绝。
两种情形覆盖所有输入，包含端点相等的边界；alpha 或 beta 恰好为小分母有理数
时，开区间的约定没有改变。

若端点最大位数为 B，j*alpha 的分子分母、每个候选值及构造后的四整数的位数
均为 O(B+log(Q+1))。Q 次取整和比较、一次约分及一次扩展欧几里得运算，
因此具有关于数值 Q 和 B 的固定多项式位成本。
对本稿取 Q=2n，端点位数已在第 4.1 节控制为 poly(n)，构造仍为 poly(n)。

**推论 3.6。** gamma 无理，当且仅当上述算法在无界多个 n 上输出整层拒绝证书。

证明：若 gamma 有理，定理 3.1 使充分大层全部接受，故拒绝层有界。
反之，若拒绝层有界，有限二择构造使充分大层全部存在接受值，定理 3.5 推出
这些有理值相邻稳定且等于 gamma。因此 gamma 无理必使拒绝层无界。证毕。

这里补齐的是单层证书的存在性、完备性与构造成本。推论也明确揭示剩余任务：
“拒绝证书在无界多层出现”与无理性本身等价，尚不能由单层算法的总定义性推出。

## 4. 表示与完整计算成本

### 4.1 计算轨迹的多项式界

D_n<8^n，binom(n,i)≤2^n。将 T_n 展开为至多 2n(n+1) 个整数项
`binom(n,i)^2*(D_n/j)`，便可估计 D_n、B_n、T_n 和聚合指数的位数为 O(n+log(n+1))。
Z_n 另增加 p、q 的输入位数。

t=O(n^2)。每个 P_t、R_t 有理项的分子分母位数为 O(t log(n+1))。
采用逐项通分而不追求最简分母时，至多 O(nt) 项的分母位数也只相加，
中间位数可由 O(nt^2 log(n+1))=O(n^5 log(n+1)) 控制。
构造有理项、聚合指数和通分需要多项式多个学校整数运算；
若把每次运算展开成位运算轨迹，轨迹总位长及检查时间仍为固定多项式。
这一结论关于数值 n 以及 p、q 的输入位数；不是关于 log n 的多项式时间声明。

因此第 3 节是真正有限、具有多项式计算轨迹的源证书构造。
将这些算术计算轨迹转换成当前 PA 完整载荷证明，还须单独给出证明转换及其长度界；
第 3 节和本节没有把“可计算地核验”直接等同于该转换已经完成。

### 4.2 为什么必须使用幂积表示

对 n≥1，取 i=floor((n−1)/2)，k=j=i+1。由 2i+1≤n，
这个三元组是 S_n 原乘积中的合法项。j 整除 D_n，该项指数至少为
`2*binom(n,i)^2`，底数 n+k≥2。

中央二项式系数至少为 2^n/(n+1)。当 n 为奇数时所取 i 位于中央；
当 n=2m 为偶数时，所取系数是中央系数的 m/(m+1) 倍，至少为其一半。
因此

```text
log2 S_n ≥ 2*binom(n,i)^2 ≥ 4^n/[2(n+1)^2]。
```

完整写出 S_n 的二进制展开需要指数位数，无法作为关于 n 的多项式大小输出。
聚合幂积则只需 n 个底数及其指数，本构造据此计算 log 的有理区间。
这个长度下界只否定要求完整输出 S_n 的方案，不是对所有 PA 证明长度的下界。

### 4.3 选定具体源句，并构造真、假两侧的短 PA 证明

现在消除一个此前保留的源端义务。第 3 节的 C(p,q,n) 是有限算法的接受判断，
还不是指定的 PA 公式。这里为每组输入明确选择一个闭算术公式 Phi_(p,q,n)，
而不是将“存在某个接受轨迹”的否定误当作可直接检查的原子。

先运行固定的完整计算日程，得到 D_n、B_n、T_n、e_(n,k)、Z_n、L_n、U_n。
即使最后比较拒绝，也保留这一日程；q≤2n 等接受条件统一放在末尾。
将每个中间自然数写成短二进制数词。有符号整数用正、负两部分表示，
有理数用分子及严格正的分母表示。每次运算展开成下列类型的闭算术关系：

- 加法或乘法结果：x+y=z，x*y=z；
- 商余检查：x=y*z+r，r<y，0<y；
- 有理数等式及比较：交叉相乘后得到上述等式、< 或 ≤；
- 程序实际采用的分支及终止条件：其具体闭比较；
- 最后的 q≤2n 与第 (3.4) 式中的两个严格比较。

幂运算展开为逐步乘法，lcm/gcd 展开为实际欧几里得算法的商余轨迹，
有限求和展开为实际累加轨迹；不在原子中留下未计算的高阶算法谓词。
所有非最终原子由完整日程生成，标准值为真。将这些原子及最终比较按固定顺序
右结合成合取 Phi_(p,q,n)。因此在标准自然数中，

```text
Phi_(p,q,n) 为真 IFF 有限检查 C(p,q,n) 接受。          (4.1)
```

若拒绝，则至少一个最终比较为假；这里不存在对任意未知接受轨迹做否定推理的问题。
该 Phi 是一个由规范日程产生的闭公式族，大小包括全部中间数词及关系。
本节不声称已在 PA 内证明它与另一个预先指定的、含存在量词的运行谓词逐点等价。

下面核算证明长度。设 m 为原子数，W 是所有原子中数值的最大位数加一。
经过上述逐步展开，每个原子只有固定数目的加、乘和比较操作，
故其短数词总位数及项编码均由 K0*(W+1) 控制。第 4.1 节给出 m、W
关于 n 和 p、q 输入位数的固定多项式界。

**闭算术原子基元。** 存在固定常数 K1、e，使每个上述真原子都有完整载荷
不超过 K1*(W+1)^e 的 PA 证明；每个假原子的否定也有同样形式的界。
构造使用按位加法的进位关系、学校乘法的部分积与加法，以及自然数序比较的差值见证。
每次只对具体数词实例化固定的 PA 等式和序模板；加法有 O(W) 个位步骤，
乘法有 O(W^2) 个部分积，所有中间数词位数为 O(W)。
将这些固定模板推导列成序列并用第 5 节的 cut 结构组合，避免复制以前的大推导。
不相等或否定序关系由相反方向的比较及差值等式给出，再接固定逻辑模板。
因此模板数、每份实例的编码以及最终证书均为 W 的固定多项式。
当前六类闭原子的具体实现和计量分别见
`FoundationCompactPAClosedAtomicCompiler.lean` 与其 `Bounds` 文件；
本节只使用该既有原子层，不依赖尚未完成的 M11 运行矩阵编译。

令 S 为 Phi 的全部公式编码长度。由短数词表示，S≤K2*m*(W+1)。
若所有原子为真，逐个编译后合取。当前合取构造保留两侧证明各一次，
每次新增开销不超过 144+11*conjunctionSyntaxBudget，且该预算受 K3*(S+1) 控制。
共 m−1 次，故总完整载荷可由

```text
m*K1*(W+1)^e + K4*m*(S+1)                        (4.2)
```

控制。这里使用的是每次对输入长度系数为 1 的加性界，
不是把任意多项式组合反复 m 次后仍未经证明称为多项式。

若某个原子 A_j 为假，先编译 NOT A_j。
NOT Phi 在否定正规形中是各 NOT A_i 的析取，沿其固定路径反复引入析取即可。
每一步保留已有证明一次，累计新增语法开销至多 K5*m*(S+1)。
所以 NOT Phi 的完整载荷不超过

```text
K1*(W+1)^e + K5*m*(S+1)。                         (4.3)
```

由 m、W、S 的多项式界，(4.2)、(4.3) 均关于 n 和输入位数多项式有界。
这完成了所选规范闭源句的真、假两侧短证明构造。
它没有证明 G_n，也没有赋予一般假运行谓词一个免费的短否定证明。

### 4.4 目标公式本身的长度

P_direct 是固定公式，G_n 只把它的两个公共参数替换为
rho_d(n) 和固定 falsumCode 的短二进制数词，再作否定。
对固定 d，rho_d(n) 的位数为 O(n log(n+1))。
替换位置数由固定公式决定，故 G_n 及其编码位数关于 n 多项式有界。
这个语法大小界不提供 G_n 的证明；它只是第 7 节组合成本的输入。

## 5. 带 cut 的闭证明序列可避免指数树复制

以下引理处理局部的表示转换，不把任意 PA 推导的全部规则混入结论。
设 phi_1,…,phi_m 是闭公式序列，最后一行为 phi_m；每一行或者是携带
当前系统公理证书的 PA 公理，或者由两个较早行 A 和 A IMPLIES B 得到 B。

设 S 计入全部行公式的编码长度与公理证书长度。定义有限序列集合

```text
Gamma_i = {NOT phi_1,…,NOT phi_i,phi_m}。
```

Gamma_m 含 phi_m 和 NOT phi_m，有一个封闭叶证明。假设已构造 Gamma_i 的树，
构造 Gamma_(i−1) UNION {phi_i} 的局部树，再以 phi_i 做一次 cut，
就得到 Gamma_(i−1) 的树。

公理行直接使用公理叶。若该行为 MP 的结论 B，局部上下文包含
NOT A、NOT(A IMPLIES B) 和 B。其中 NOT(A IMPLIES B) 是 A AND NOT B；
一次合取规则分成两个分支，分别由 A 与 NOT A、B 与 NOT B 封闭。
需要的公式恒等按系统既定的经典否定正规形式解释。

从 i=m 向 1 逆序完成后得到单元素结论 {phi_m}。
关键是每次 cut 只使用已有大树一次；公理或 MP 的另一侧是新的局部小树。
因此树节点数为 O(m)，每个序列的公式内容受 O(S) 控制；
完整序列树和结构证书可用 K*(S+1)^2 的粗界控制。
这里 S 按编码长度计量，编码常量吸收到 K。

这解决了闭公理加 MP 序列的复制问题。含自由变量、全称推广的完整模拟仍需
证明逐行全称闭包及相应量词变换；本引理不替代当前 P 的 PA 内部化条件。

### 5.1 当前完整载荷的五节点 MP 构造

还可以直接对当前列表格式给出更紧的局部账本。令 I=A IMPLIES B，
两份已接受的输入分别证明 I、A，树为 T_I、T_A，结构证书为 C_I、C_A。
构造如下，每个输入子树及其证书只出现一次：

```text
cut，结论列表 [B]，切公式 I
├─ wk，结论列表 [I,B]
│  └─ T_I
└─ and，结论列表 [NOT I,B]，分解 NOT I=A AND NOT B
   ├─ wk，结论列表 [A,NOT I,B]
   │  └─ T_A
   └─ closed，结论列表 [NOT B,NOT I,B]，互补公式 B。
```

证书为 `binary (unary C_I) (binary (unary C_A) leaf)`。
两个弱化节点只检查原结论集包含于新列表；合取两侧、封闭叶及 cut 两侧的
结论集合逐项符合规则，根结论恰为 B。这是语法验收，不调用 PA 语义可靠性。

记 a、b、i、j、nb 分别为 A、B、I、NOT I、NOT B 的 raw token 流的
binaryNat 载荷长度，均不包含各自公式码的 sentinel。
当前自然数标签编码位长是 `2*Nat.size(tag)+2`。
新增树的五个规则标签共 34 位，五个列表长度头共 28 位，故新增树位数是

```text
62+2a+2i+3j+2nb+6b。
```

新增结构证书的两个 binary 标签、两个 unary 标签和 leaf 标签共 26 位。
因此新增完整载荷是 `88+2a+2i+3j+2nb+6b`。
由当前公式编码的析取、合取标签均占 8 位，

```text
i=8+|NOT A|+b，j=8+a+|NOT B|，
|NOT A|≤2a，|NOT B|≤2b。
```

否定的因子 2 可按公式树归纳：复合连接词标签等长，量词标签等长，
正负原子标签的变化至多使该标签长度翻倍，其他项编码不变。
将这些等式和界代入，得到

```text
L_out ≤ L_I+L_A+128+9a+18b。
```

两份输入完整载荷均≤n 时，其根公式给出 a≤n；B 是 I 的子公式，所以 b≤n。
因此

```text
L_out ≤ 29n+128。                                  (5.1)
```

若接受码需先作规范重编码，使用已核查的“不增加完整载荷”性质。
这里载荷指 sentinel 前的完整树与结构证书，未遗漏证书成本。
本账本对应 `FoundationCompactProofTokenMachine.lean`、
`FoundationCompactPAAxiomCertificate.lean` 的编码定义。
已有 `FoundationCompactCertifiedModusPonens.lean` 中
`acceptedCodes_modusPonens_exists` 对另一构造给出较松的外部界
`L_I+L_A+240+34*SyntaxBudget`；SyntaxBudget≤9n 时可得 308n+240。
本稿的新常数是纸面账本，不声称已将该更紧版本形式化。

### 5.2 从外部 MP 到内部条件 (3) 的剩余句子

(5.1) 本身不能直接作为 PA 内部 (3)。还需要在 PA 内统一证明：

1. 输入的直接矩阵见证确实解码到两个通过检查的树、证书及相应根公式，
   inputWidth 是完整载荷长度。
2. 数字编码上的五节点构造保持可解析性和证书验收，输出根公式码是 code(B)。
3. PA 内的位长账本给出输出 inputWidth≤29n+128。
4. 对这个输出码构造全部规范表格以及规定燃料下的接受运行见证，
   满足同一 AcceptedPayloadMatrix 与 AcceptedConclusionRow。
5. 引回输出矩阵的 20 个存在量词。

这样才得到同一直接谓词的内部 MP 蕴含。
这里其余 19 个外层存在见证没有多项式大小要求：公式只限制 inputWidth。
不能把完整轨迹的外部多项式大小误当作条件 (3) 本身的必要前提；
但必须在 PA 中证明这些见证存在且符合规定矩阵，不能以 Lean 元理论 exactness 代替。
完成统一 PA 推导后，还须通过短数词实例化和公式码计算核算 p3 的长度。

### 5.3 内部编码层：规范 token 表与原始载荷的双向对应

这里补出 5.2 中编码层的一条局部 PA 归纳证明。
实际关系是 `compactCanonicalPackedTokenStreamTableauAtWidthDef`，
以及 `compactFixedWidthEntryDef`、`compactBinaryNatTokenSegmentDef`；
不是另选一个仅在标准模型中等价的编码。
记 E(k)=2^k，ell(t) 为二进制长度。E、ell、商余和位函数只是可消去的算术定义缩写。
实际 expDef、lengthDef 的存在唯一性及位关系的商余刻画可由算术归纳得到；
相应基础论证也见 Foundation 的 Arithmetic/Exponential/Exp、Log、Bit 文件。
以下各步使用一阶算术归纳与商余唯一性，不将 Nat.testBit 的外部等价作为 PA 公理。

**行提取。** 定义 Row(T,W,i)=(T div E(iW)) mod E(W)。PA 可证明

```text
Entry(T,W,i,v) IFF v=Row(T,W,i)。
```

商余给 Row<E(W)。将 T 写成
`u*E((i+1)W)+Row*E(iW)+r`，r<E(iW)，
即可逐位证明 Row 的前 W 位正是 T 的第 i 行。
反之，Entry 保证 v<E(W)，并给前 W 位相等。
有限位外延性按 W 归纳：W=0 时两数均为零；W+1 时最低位相等，
除以 2 后两商的前 W 位相等，归纳推出两商相等，再还原原数。
Entry 原公式中的长度见证取 ell(v)，其有界要求由 ell(v)≤v 满足。

这个结论不说原表本身就是规范表；当前关系没有限制所用行以上的高位。
正确结论是已指定行的值唯一，且可另构造具有同样这些行的规范表。

**单个 token。** 对 s=ell(t)，递推

```text
D_0=0，
D_(j+1)=D_j+E(2j)+bit(t,j)*E(2j+1)，j<s，
word(t)=D_s，w(t)=2s+2。
```

按 j 归纳，D_j<E(2j)，其第 2k 位为 1、第 2k+1 位为 bit(t,k)，k<j。
归纳步只在新的两位加入 E(2j) 或 3E(2j)，不改变较低位。
因此 word(t) 正是原 binaryNatCode 的 `(1,bit)` 对及末尾 `00` 的数值。
令 Segment(p,o,t,o') 为原段关系，逐一使用 marker、data、末尾两个零的条款，
再用有限位外延性，得到

```text
o'=o+w(t)，
(p div E(o)) mod E(w(t))=word(t)。                (5.2)
```

t=0 时 s=0、word=0、w=2，对应唯一的 `00` 段，也包含在该证明中。

**完整前缀。** 从 AtWidth(c,m,T,O,W) 消去见证取得 p，
原矩阵保证 p<E(W)、c=p+E(W)。取 t_i=Row(T,W,i)，o_i=Row(O,W,i)，并递推

```text
L_0=V_0=0，
L_(i+1)=L_i+w(t_i)，
V_(i+1)=V_i+E(L_i)*word(t_i)。
```

PA 对 i≤m 证明不变量

```text
o_i=L_i，p mod E(L_i)=V_i，V_i<E(L_i)。           (5.3)
```

基例由首 offset 为零得到。归纳步先由行唯一性，将段关系中的见证换为 t_i、o_i、o_(i+1)。
然后应用 (5.2) 和商余恒等式

```text
p mod E(o+w)
 = (p mod E(o))+E(o)*((p div E(o)) mod E(w))。    (5.4)
```

(5.4) 的证明是连续作两次带余除法：p=qE(o)+r、q=uE(w)+v，
r<E(o)、v<E(w)。于是 p=uE(o+w)+vE(o)+r，
且 vE(o)+r<E(o+w)，由余数唯一性得式。
这同时保持 (5.3) 的数值等式和严格上界。

末 offset 为 W，故 L_m=W。原 p<E(W) 再给出

```text
p=V_m，c=V_m+E(L_m)。                           (5.5)
```

右边正是实际 token 顺序拼接并添加 sentinel 的代码。
末尾 `00` 可以使 payload 数值有高位零；本证明保留 W，
没有把 payload 数值的二进制长度误当完整载荷长度。

**递推见证存在。** 上述前缀递推也可以显式编码，不用黑箱宣称任意递归自动可表示。
输入行满足 ell(t_i)≤W，取 B=m*(2W+2)、H=B+1，则
L_i≤B，V_i<E(B)<E(H)。
按 i 归纳建立宽度 H 的两个表格，分别存储已经生成的 L、V，保持
每个表 Q_i<E((i+1)H)。增加一个新值 a<E(H) 时取

```text
Q_(i+1)=Q_i+a*E((i+1)H)。
```

带余除法验证旧行不变、新行等于 a，且新表小于 E((i+2)H)。
word 的中间递推也可用同一办法，行宽取 2W+3 即足够。
因此 PA 的归纳步骤每次都有实际自然数见证，归纳结论提供整个前缀表。

**反向规范表。** 给定一份有限 token 序列及上述前缀编码，令 W=L_m、p=V_m，
构造 T*=sum(i<m) t_i E(iW)、O*=sum(i≤m) L_i E(iW)。
这些和用同一逐行追加构造实现。每个 token 的宽度至少 2，故 W≥2m。
各 token 的长度不超过 W；offset 不超过 W，且 W<E(W)。
因此各行均放得入宽度 W。逐行验证 Entry、Segment，
首尾 offset 正确，m≤W+1，p<E(W)，再取 c=p+E(W)。
原 AtWidth 的 payload、sentinel 等存在量词均满足其 ≤c 的界。
空序列单独取 m=W=p=0、c=1、T*=O*=0，即满足全部条件。

由此得到规范 token 表的 PA 内部构造与逆向提取的纸面证明。
它本身未处理真实 proof/certificate 的规则检查、状态机全部分支及燃料计数。
燃料充分性另在第 5.4 节证明；实际规则矩阵对应仍未闭合，不能由编码引理宣布 (3) 完成。

### 5.4 规定燃料充分：势函数与五节点 MP 的准确步数

这里的机器是实际 `compactNumericVerifierStep`。一次外层 parse 或 combine
是一个宏步，内含字段解析或规则检查；下述线性计数不宣称内部运算时间线性。
记当前剩余 proof token 列表为 P，任务栈为 K，初始 proof/certificate token 数
分别为 p0、c0。规定燃料为 F=4*(p0+c0+1)+8。

首先，成功的节点解析至少消耗一个 proof token。外层先消耗规则 tag，余下
字段解析器只返回其输入后缀：语法解析机可以维护游标 d，使剩余列表为原列表
的 drop(d)；每个分支只保留或截短列表，repeat-frame 只改变任务栈。
按内部运行步数归纳，随后按字段组合顺序归纳，便得到完整节点的严格缩短。
游标、drop 和后缀等式可用第 5.3 节的有限行表编码在 PA 中作同一归纳。

对 running 状态取自然数势函数

```text
Phi=3*length(P)+length(K)。
```

只需检查一步前后均仍在运行的情形。弹出当前任务后：叶 parse 不添加任务，
单子节点 parse 添加 Parse、Combine 两项，双子节点添加 Parse、Parse、Combine
三项。故对应任务栈净变化为 -1、+1、+2，而 proof 长度均至少减 1；势函数分别
至少减 4、2、1。combine 保留 proof 列表、弹出任务，势函数恰减 1。
分支失败或 Finish 已经停机。停机状态在实际 Step 中保持不变。

对运行索引 j 作 PA 归纳：若第 j 状态仍在运行，则此前状态均在运行，且
`Phi(s_j)+j≤Phi(s_0)`。因此第 Phi(s_0)+1 步不能仍在运行。
初态只有一个 Parse，故在 3*p0+2≤F 步内必停机。这证明燃料不会在机器仍运行时
耗尽；它不把拒绝状态变成接受状态。

对形状匹配的证明树和结构证书，更准确的遍历代价是

```text
S(leaf)=1；S(unary(T))=S(T)+2；
S(binary(L,R))=S(L)+S(R)+2。
```

加强归纳命题允许任意 proof/certificate 后缀、剩余任务栈和旧值栈：从一个 Parse
任务开始，S 步正好消费该树及证书，将 `(根结论,局部检查结果)` 压入旧值栈，
其余后缀和任务逐字保留。叶是一次 parse；单子节点是 parse、子树、combine；
双子节点是 parse、左子树、右子树、combine，合并时栈头次序为右结果、左结果。
该续延归纳既证明步数，也说明不会复制输入子树。

于是 S=N+I≤2P，其中 N 是节点数，I 是非叶节点数，P 是 proof token 数。
空后缀情况下再一步 Finish 得到验收布尔值；若局部规则检查全部通过，S+1 步即接受。
后续停机状态吸收，故可以填充到恰好 F 步。实际 accepted-trace 有 F 行，
第 F-1 行的 next state 是第 F 状态，末行约定没有差一。

主稿五节点 MP 的 cut、and、两个 wk、一个 closed 共新增五次 parse；前四个节点
各另需一次 combine。因此

```text
S_out=S_I+S_A+9，接受前含 Finish 共 S_I+S_A+10 步。
```

每个新增节点至少贡献一个 proof tag。若 P_out=P_I+P_A+H，则 H≥5，因而

```text
S_out+1≤2P_I+2P_A+10≤2P_out≤4*(P_out+C_out+1)+8。
```

这补齐规定燃料的数值充分性。完整实际状态定义与逐分支纸面归纳见
[燃料引理](../docs/paper_mp_fuel_lemma_20260905_zh.md)。输入切分的 PA 内计数校准
在第 5.5 节补齐，实际接受行的吸收补行在第 5.6 节构造。
仍须构造成功 parse/combine 的原矩阵见证；步数计数不替代这些规则验收义务。

### 5.5 同一 InputSplit 的长度校准与规范输入表

记 raw 表宽为 W、token 数为 M，初态 proof、certificate 长度分别为 p、c。
实际 StateCore 的前两个 NatListSlice 给出

```text
e5=e3+1+p，e7=e5+1+c。
```

由第 5.3 节的行提取和有限位外延性，实际 CrossEq 在 PA 内恰等价于
两个 slice 具有相同长度、满足原端点界且对应 Row 值相同。
不同表宽的超出位均补零；两宽均为 0 时，两个行值同为 0。

初态 source/proof 比较给 proofFinish=proofStart+1+p，
InputSplit 的 raw 前半比较给 proofFinish=proofStart+1+split。
自然数加法消去得 p=split。证书端同样给 M=split+c，所以

```text
M=p+c。
```

逐项对应也成立：前半 raw 第 i 行先等于 source 的 proofStart+1+i 行，
再用初态比较的 offset=1+i 得到 proof 第 i 项；后半令 j=i-split，
依次用 offset=j 和 1+j 得到 certificate 第 j 项。
故原 raw 流在 PA 内恰为 proof++certificate，公开燃料恰为 4*(p+c+1)+8。
这没有先假设两个列表满足证明树语法。

反方向给定两列表，以 M=p+c，W=2*sum(ell(token)+1) 构造 raw 表。
source 是 [p]++proof++[c]++certificate，规范宽度 H 满足

```text
2M≤W，H=W+2ell(p)+2ell(c)+4≤3W+4。
```

取 split=p、proofStart=0、proofFinish=certificateStart=p+1、
certificateFinish=M+2，逐行复制即给原 InputSplit 的新规范见证。
固定宽度追加不变量给三张表的位数界

```text
ell(rawTable)≤M*W，ell(offsetTable)≤(M+1)*W，
ell(sourceTable)≤(M+2)*(3W+4)。
```

空流 W=M=p=c=0 时 H=4，source=[0,0]，三表均为 0，原条件仍成立。
这些是新构造表的界，不是任意满足原式的宽表或含额外高位表的界。
完整逐式证明见 [InputSplit 引理](../docs/paper_direct_input_split_20260905_zh.md)。

### 5.6 实际 429 列矩阵的重编码、接缝与吸收补行

令 G 是原 compactNumericVerifierStepGraphDef，e 为其 429 个数值参数。
外层表宽为 U，定义

```text
Read(U,T,i,j)=(T div 2^((429*i+j)*U)) mod 2^U，j<429。
```

原 Entry 的唯一性逐个消去一行的 429 个有界存在量，得到固定 PA 等价：
原 BoundedRow 当且仅当 G(Read(U,T,i,0),...,Read(U,T,i,428))。
反向见证都是小于 2^U 的 Read，满足原 ≤2^U 界。
邻接关系同理精确变成源行 [0,1,2,24,25] 与下一行 [0,1,2,3,4]
进入同一个原 CrossEq；这一步不引入另一个机器语义关系。

将 N 行的声明单元依次读为 a_j，在宽度 V≥U 下递推
T_0=0、T_(j+1)=T_j+a_j*2^(V*j)。PA 归纳维护 T_j<2^(V*j)
及所有旧单元保持，得到重新打包的同一行序列。
两段轨迹可在共同外层宽度下依次打包：内部邻接由各段保留，唯一接缝须另证原 CrossEq。
不能直接相加任意旧表码，因为它们可能宽度不同或带有声明区域外的高位。

下面把“停机吸收”落实为原公式的一行见证。G 的每个析取分支都包含 next StateCore。
若 G(e) 且 e36=e38=1，令

```text
h[j]=e[j]，j=0,1,2；
h[j]=e[j+21]，3≤j≤23；
h[j]=e[j]，24≤j≤44；
h[j]=0，45≤j≤428。
```

h 的两个 core 都等于 e 的 next core，currentStatusTag 为 1。
该 core 给 e24≤e25≤e2；以 count=e25-e24 作见证，同切片 SliceEq
逐位为同一个原子与自身等价。因此 h 满足原 halted 分支，从而 G(h)，
且 h36=h38=1。源 e 到 h、h 到 h 的 CrossEq 接缝同样成立。
AcceptedConclusionRow 读取的列 0,1,2,34,35,44 全部保持，内部结论见证可原样使用。
故已有 t>0 行的实际接受矩阵可追加 F-t 个 h，补到任意 F≥t，保留同一结论。

单个 combine TaskCore 的 suffix 追加也可直接构造：复制前四字段，
把 suffix 长度头 k 改为 k+r，并追加 r 个新 token。
所有平移后的 Gamma 边界必须按新的内部 tokenCount 重编码；其原行宽就是 tokenCount。
原样复制旧任务会使 TaskCrossTableBridgeGraph 的第五字段 CrossEq 失败，
因为新旧 suffix 的长度头不同。

这些是矩阵层的局部构造。五类 proof-root 成功终点图及 certificate-node 成功终点图
的 suffix 输运现由第 5.7 节补齐；完整内部 MP 还须重建整个任务/值栈，
构造外层调度与规则行，并提取 Finish 前的成功运行段。
详见 [实际矩阵输运](../docs/paper_direct_mp_transport_20260905_zh.md)；条件 (3) 尚未闭合。

### 5.7 原解析成功终点的追加：逐分支 PA 构造

这里证明实际成功终点可把输入 X、返回后缀 Y 同时改为 X++R、Y++R，
并重新构造原算术公式的全部存在见证。它不要求任意输入都能成功解析。

先用原 Entry 唯一性和 Unit/TripleBoundary 的 PA 归纳，把每个语法解析状态读成
唯一 token 数组、任务三元组数组和 status 区间。
原 status 的三个头分别为 [0]、[1,0]、[1,1]，互斥性由实际单元读数得到。
六类 SyntaxStep 析取中，failed 状态仅可经 Done 保持 failed。
沿原给定轨迹作 PA 归纳，若某行 failed，末行也 failed；原末行 completed，
所以每一行均非 failed。这是同一有限矩阵内的推导，没有调用反射。

将每个状态的 token 数组 L 改为 L++R，任务三元组保持；
running 头保持，completed 输出 O 改为 O++R。
逐分支检查原 Step：Done、Empty 的 SameRows 两侧同时追加；
Repeat 的任务计数和值保持；成功 Term/Formula 只读旧输入的前 1、2 或 3 项，
旧的长度下界在追加后仍成立。实际 DropRows 含 c≤|L| 及 |L|=c+|Y|，
故尾部关系逐项变成 DropRows(L++R,Y++R,c)。失败分支已由前段排除。
七个分支 slot 中的 token 值、binder 保持，boundary 与输出 count 按新布局重建。

令 f(t)=16*(t+1)^2+8。旧轨迹有 f(|X|)+1 个状态，
新输入要求恰 f(|X|+|R|)+1 个状态。
先输运所有旧行，再用实际 Done/completed 分支补齐，多余行仍引用新完成输出。
所有背景块、端点块和状态块的原始 token 长度先确定，共同选最终 tokenCount，
然后按此行宽重编码各边界，并从内到外选择幂界。
这样新 endpoint 的 exact fuel、初末关系和所有 bounded 行同时成立。

ClosedSuccess 的额外 guard 也须检查。原 guard 是
TermRows IMPLIES (currentCount≤1 OR slot4≠1)。
成功 Term 已有 currentCount≥2，所以旧 guard 实际给 slot4≠1，新行保留该数值。
其他成功分支的任务头或 status 与 Term 不相容，追加后其前件仍假。
因此闭公式终点具有同一输运，而不是把整个“闭公式++R”误认成闭公式。

Sequent 解析由 m 条普通语法终点及 m+1 个 suffix 组成。
对每个 suffix S_j 同加 R，保留已消费的公式 A_j，
原 Append(A_j,S_(j+1),S_j) 逐项变成 Append(A_j,S_(j+1)++R,S_j++R)。
按 b_(j+1)=b_j+1+|S_j|+|R| 连续放置各个带头 suffix，
准确保持原公式中 index+1 同时作为 currentFinish、nextStart 的约定。
Gamma 的总头 m 及各 A_j 内容保持；各内层 parser 使用同一个最终公共表布局。

五类 proof-root 图由上述 sequent 终点和零至两个语法终点固定次数合成：
SequentOnly 无额外解析；OneFormula 使用原 binder 参数；ClosedFormula 使用上述 guard；
TwoFormula 两次使用 (taskKind,binderArity,repeatCount)=(1,0,0)；
FormulaTerm 依次使用 (1,1,0)、(0,0,0)，第二次保留 witness 字段。
由此保持 tag、Gamma、first、second、witness，仅追加 root suffix，
再引回原 Bounded/Tagged 包装。完整构造见
[解析终点追加证明](../docs/paper_direct_parser_append_20260905_zh.md)。

certificate-node 的四类分支也可在同一布局中输运。
simple、fixed PA、symbol PA 只需重建原 Cons、Append、At 及单位边界；
induction PA 唯一的递归项恰为普通语法终点 (1,1,0)，由上面引理处理。
新 input/suffix 同加 R，certificateTag 和 PA 分支已消费的 axiomTokens 保持，
原 6/15/17/21 项有界见证逐项重建。
simple 分支不约束 axiom/formula 端点，不能额外推它们一定指向合法空列表。
详见 [证书节点追加证明](../docs/paper_direct_certificate_append_20260905_zh.md)。

本节消去 parser 成功图的输运缺口。任务栈、one/two schedule 与 Finish 前缀
进一步在第 5.8 节补齐，值栈和完整 one/two 行在第 5.9 节补齐；
其余规则分支及全运行组装仍不能据此省略。

### 5.8 任务栈续延与 Finish 前成功片段

先解决完整任务切片相等时的字段分界。实际 TaskCore 从起点 a 依次存放
tag、Gamma 和 first/second/witness/suffix 四个带头列表。
Gamma 的边界满足 g_0=a+2、g_(j+1)=g_j+1+n_j，n_j 是第 j 个真实长度头。
因此两条合法任务的整片读数相等，按 j 作 PA 归纳就得到相同 Gamma 分界；
再用四次 finish=start+1+count，得到所有字段的相对边界与正文相同。
不需要先证明 Gamma 中每一项具有逻辑公式语法。

定义 eta_R：tag=10 的任务全部保留；其他任务只给 suffix 加 R。
已满足 ParseShape 的任务仍是六个 token [10,0,0,0,0,0]。
一般 TaskCore 的 tag=10 不自动保证空字段，所以不能在这里强制清空旧任务。
由前段的边界刚性，相等的两任务经 eta_R 后仍逐字相等。

给两栈尾部同加 K0，构造 map(eta_R,K)++K0；K0 本身不再施加 eta_R。
若旧 ReplaceHeadRows 的计数为 s+p=t+1，新计数满足 (s+c)+p=(t+c)+1。
其比较 source[1+i] 与 target[p+i] 的全称分为旧尾与新增尾：
旧尾使用原行等式；新增尾令 j=1+i-s，由计数式得 p+i=t+j，
两边都是 K0[j]。DropRows 的 s=d+t 同理给 d+i=s+(i-t)，
将新增索引准确对齐。规范边界与每行 14 项见证按最终 tokenCount 重建。

one/two schedule 分别取 p=2、3，前缀为 Parse/combine 或 Parse/Parse/combine。
新 Parse 保持全空，combine 和 parser 输出根同时施加 eta_R，
五字段的完整 TaskCrossTableBridge 因而保持。
实际 combine.tag=rootTag 来自这个跨表桥，不能只由裸 schedule 的标签析取得到。
逐项构造见 [任务栈与调度输运](../docs/paper_direct_schedule_transport_20260905_zh.md)。

还可以在原接受矩阵内严格取出 Finish 前片段。
先从 StateCore 的平列表、Gamma、Task/ChildResult、两栈的固定层级归纳证明：
整状态 CrossEq 推出 statusTag 相同，且仅在 tag=1 时推出 statusBool 相同。
running 的 statusBool 原本不受约束，不能只看到 bool=0 就判失败。

原 G 的 Halted 分支保持整个状态；parse/combine 成功分支的 nextTag 都为 0，
失败分支的 nextTag=1、nextBool=0。由相邻 CrossEq 和 status 刚性，
一旦 failed 就沿给定有限矩阵保持 failed，与最后接受行矛盾。
在 i<F 中取 nextTag=1 的最小 k，初态 tag=0 保证此前全 running。
第 k 行不是 failed，其 nextBool=1；逐析取排除其他分支后，只剩成功 Finish。
此后全部 Halted，因此这是唯一 Finish 行。

初态 taskCount=1，而 Finish 要求 taskCount=0，所以 1≤k<F。
成功 Finish 的原合取还给两流为空、任务栈为空、值栈仅有一个 true 子结果。
截取前 k 行的原 429 列读数，保留每行 G、原初态和全部 CrossEq 接缝；
末态仍 running，下一步 Finish 留在片段之外。
若输入带 AcceptedConclusionRow，其指定公式集合也能传回这个子结果，
但不能把“值栈只有一个结果”误读成“Gamma 只有一个公式项”，后者可有重复。
完整推导见 [成功 Finish 前缀](../docs/paper_direct_finish_prefix_20260905_zh.md)。

上述两项是原矩阵的 PA 内纸面引理。下一节进一步接上值栈和两个非叶分支；
完整 (3) 仍须处理其余实际规则与新 MP 节点的全段组装。

### 5.9 值栈续延与 one/two 成功行的完整 429 列构造

原 ChildResultCore 把一条子结果存成带头 Gamma 后接一个 Boolean 单元。
Gamma 为 A_0,…,A_(g-1) 时，其真实 token 块为

`[g] ++ [|A_0|] ++ A_0 ++ ... ++ [|A_(g-1)|] ++ A_(g-1) ++ [b]`。

旧 BoolSlice 给 b∈{0,1}。复制这些单元，先确定共同新 tokenCount N'，
再以 N' 为条目宽度重编码 Gamma boundary；空 Gamma 的块为 [0,b]，
boundary 仍包含一个真实地址，不能置零。逐项前缀归纳给新 ChildResultCore。
对原 RowsEq 的两个 Gamma，按公式索引复制相同带头切片，保留 b，
重建全部 14 个局部见证及四个 Entry，即得到新 BoundedRowsEq。
HeadEq 同样处理；其 expectedGamma 布局来自调用它的 TaskCore 或规则图。

令原值栈计数为 a、b，新共同尾 V0 的计数为 c。
DropRows(d) 的 a=d+b 变成 a+c=d+(b+c)；新增索引 i=b+j 时，
source[d+i]=source[a+j] 与 target[b+j] 都是 V0[j]。
PushDropRows(d) 的实际计数式为 d≤a、a+1=d+b、b≥1。
新 target 第 0 项仍是原新头；对 d+i<a+c 的尾比较，
若 d+i<a，搬运旧 RowsEq；否则 j=d+i-a<c，且 i+1=b+j，
两边仍是 V0[j]。这给原 Drop/PushDrop 的全部有界全称，包含空源和全弹出情形。

现在给定原 one/two parse-success 行 e。它的两条输入 CrossEq 及成功 parser
给当前 P、C；CommonRows 的两条返回 CrossEq 给下一状态 P1、C1。
分别追加任意 R、S，同时把两条任务栈变成 map(eta_R,K)++K0，
把两条值栈变成 V++V0。新流的头改成新 count，正文逐单元相同，故原 CrossEq 保持。
CommonRows 的值栈 DropRows(0) 由前段构造给出。
取同一个 H_t 容纳两边任务见证、同一个 H_v 容纳两边值见证，
两边都用 2^H_t、2^H_v，满足原 CommonRows 的四个保持等式。

两条状态按原布局写两条流、两栈和最后的 [0]，从而满足原 running StateCore。
这个分支没有存储 statusBool，因此其两个外部未读坐标可取 0。
当前 Parse 头只从原 Frame 得到 tag=10，保留它原来可能非空的全部字段；
schedule 新生 Parse 才是六单元空字段形式。
parser 状态、root、证书和两条外层状态共同确定原始 token 布局，
随后统一确定 N' 和所有 boundary，避免更改 N' 后沿用旧 boundary。

one 的实际 TagMatch 强制证书标签为 2，two 强制为 3，故原证书图只能选 simple。
它不读取 axiom/formula 坐标，这些见证可取 0，不声称它们是合法空列表。
原 proof-root 成功图和第 5.8 节 schedule 同时给根与 combine 的 suffix 加 R，
完整五字段跨表桥保持。这样逐项得到原 88 参数 one 或 102 参数 two NonLeaf 图。

原 G 的全部 429 列由同一组构造值赋值：0—44 放共同表及两个 StateCore，
45—58 放当前任务头，59—91 放成功 parser 和暴露的根字段，
387—400 放 firstParse，415—428 放 combine。
two 还在 401—414 放 secondParse；one 的实际替换向量跳过这 14 列，可以置零。
92—386 均属于未选择的 leaf/rule 分支，可以置零。
引入原 NonLeaf、Parse success、Parse 和 G 的指定析取，再按固定宽度打包，
得到真实原 BoundedRow，未用外部 Nat verifier 的语义代替算术公式。

以上完整坐标映射、字段刚性和共享界经过对原源码的独立复核。
逐项纸面推导见 [值栈与非叶成功行输运](../docs/paper_direct_parse_state_transport_20260905_zh.md)。
本节完成两个非叶局部 G 行。下面两节继续补齐叶与 combine；
整段接缝、五个新增 MP 节点仍须另行构造，不能据此把完整条件 (3) 标为完成。

### 5.10 三个叶成功分支：保留规则图，重建实际接口

三个原叶分支为 Verum、Closed、PAAxiom，标签对分别为 2/0、0/0、1/1。
proof-root 分别使用 SequentOnly、普通 OneFormula、ClosedFormula。
Closed 叶的名称不等于 ClosedFormula parser，不能混用两个追加引理。

先给原 LeafParseSuccessTransportGraph 的共同构造。
两个 parser 的新返回后缀与 next 两流同为 Q++R、D++S，给两条实际 CrossEq。
原目标值头通过暴露七坐标、两个 boundary Entry、ChildResultCore 与根 Gamma 桥，
被识别为同一 Gamma、同一 b。新头保持此内容，重建七坐标与所有界。
任务栈 DropRows(1) 由第 5.8 节给出，值栈 PushDropRows(0,b) 由第 5.9 节给出。
两状态使用共同 H_t、2^H_t、H_v、2^H_v，原四个控制数等式保持。
共同图没有假定 b=1；规则结果 b=0 的行也须输运。

Verum 的原检查为 b≤1 且 b=1 当且仅当 Gamma 有一个完整列表块 [1,2]。
Gamma 项数、每项长度头与正文保持。成员见证的同一索引在新旧表间传递，
两个端点由 Entry 唯一性固定，所以正反两个方向都成立。
由这个双向等价保持旧 b，不能只搬运成员存在的正方向。

Closed 的 28 个独立规则参数及 resultBool 全部原数保留。
这样内部完整 29 参数 SelfContainedGraph 是旧合取中的同一个公式实例，
包括规则表容量、变换轨迹和所有界，不需要再次假定其语义可靠性。
只把新 root Gamma、first 与旧规则表的对应切片重接两条 CrossEq。
一端重编码的 CrossEq 先从旧位等式恢复单元值相等，再按新位宽引入位等式，
不直接扩大旧位全称范围。

PAAxiom 同样完整保留原 259 参数 JointLeafRows，包含 fixed、symbol 或 induction
所选端点、公理规则和所有内部轨迹。其内部 endpoint 不与外部流整体相连，
因此不追加 S；外部接口只连接 Gamma、candidate、axiomTokens 三个切片。
这三项内容分别由 proof-root 和 certificate 追加引理保持，重建三条 CrossEq，
再保留原标签与结果等式，便得到完整原 PA 叶图。

429 列中，0—91 放新状态、当前头和 parser；92—98 放目标值头，99 保留 b。
Closed 在 100—127 逐数保留旧规则块；PA 在 128—386 保留旧 JointLeafRows。
其它未选规则列及 387—428 可取 0。PA 实际接口等式为
e'[66]=e'[323]、e'[79]=e'[324]、e'[99]=e'[307]，两边同值保持。
最后引入原对应 leaf、Parse success 和 G 的析取，得到完整新行。
完整合取、坐标与边界证明见 [三个叶行输运](../docs/paper_direct_leaf_state_transport_20260905_zh.md)。

### 5.11 三个 combine 成功图与公式变换全轨迹

原 combine 的 simple、allShift、exsCut 共覆盖 And、Or、Wk、All、Shift、Exs、Cut。
它们的共同 Frame 从包含两个长度头的输入整片相等，推出两流各自相等。
追加相同 R/S 后重写长度头，输入整片仍相等；任务栈应用 DropRows(1)，
值栈依原规则应用 PushDropRows(1) 或 PushDropRows(2)，并保持原结果 Boolean。

规则字段 Gamma、first、second、witness 不变，suffix 追加 R。
原 Member、Subset、SetEq、Cons/TwoCons 集合等式及一元、二元构造成员，
都通过同一 Gamma 索引、唯一端点、长度头和逐单元等值证明双向保持。
所以规则 b=1 与条件 A 的双条件，在 b=0 时也得到保留。
这些集合图允许重复公式，不额外要求去重。

All、Shift、Exs、Cut 还需原公式变换全轨迹。
新表保留旧表前 N 个单元作前缀，在后方放新外层状态；旧变换状态原始块留原地址。
先确定新 N'，再重包所有按 N 位读取的 boundary，重算 size，统一收集并扩大内部界。
输入、输出、witness 正文及各 count 保持，所以规定 fuel 和变换 stateCount 均不变。
对原六种 syntax 分支逐行搬运：Done、Empty、Repeat、Invalid 保持状态和输出关系；
Term、Formula 保持消费数、算术 guard 和对应 OutputAppend 图。
局部失败和默认空输出也逐析取处理，不假定 transform 的 parser 总成功。

free 的参数为 mode=0、binderArity=1；shift 为 mode=1、binderArity=0；
substitute 为 mode=2、binderArity=1、实际 witness；negation 为 mode=3、binderArity=0。
它们的各个输出变换只操作保持的 token 值，或接入内容相同的新 witness。
原末态默认输出区分剩余 parser 输入和累计变换输出，不能将两者混同。

扩界后 success=false 的保持需要反向证明。
原 EmptyFinalBounded 的成功片段恰为 [1,1,0]，三项规范见证是输出起点、
唯一终点 boundary 和其位长，均≤旧 N。
原 TotalTrace 自带 H≥(N+1)N、V=2^H，故这些规范见证本来就落在旧界内。
新旧原始片段相同，因此新成功反推旧成功；扩大界不会产生旧图不承认的成功。
该反向及原公式中空列表不读取的 boundary 已逐源码独立复核。

逐公式 shift 保持每一行 success_i 和实际默认结果，并重包 successTable：
其真实条目宽度是 N，必须改为 N'，不能因值为 0/1 就按位表复制。
全成功时搬运候选与 expected 的逐项相等；失败时保留原失败索引及空 expected。
All 对 task Gamma 做 shift，Shift 则对 right premise Gamma 做 shift，两个接口分别接入。
每个 premise 还通过原 HeadEq 与真实值栈第 0 项或第 1 项相连。

完整 combine 使用 429 列的前 93 列：0—58 为状态与头，59—91 为规则、变换、
shift 与控制界，92 保留原 resultBool；93—428 在选定析取中未读，可取 0。
逐合取引入原 93 参数 CombineStateGraph，再安装到 G，闭合这三个成功分支。
详见 [完整 combine 状态输运](../docs/paper_direct_combine_state_transport_20260905_zh.md)。
至此已逐类给出运行片段内全部 Parse/Combine 成功行的续延。
下一节接齐片段本身；新 MP 节点及同一输入/结论的最后接合仍需完成，
条件 (3) 仍为开放项。

### 5.12 原成功片段的逐行续延与新燃料比较

第 5.8 节提取的 k 个 Finish 前行，两端都 running。
在原 G 中排除 Halted、Finish 及两个 failed 分支后，每行必为第 5.9—5.11 节
已经处理的五类 Parse success 或三类 Combine success。
固定后缀 R/S 和尾栈 K0/V0，逐行应用对应完整 429 列引理。

旧相邻两状态的整片 CrossEq 经固定层级游标归纳给两流、两栈内容相同。
它们经过同一个续延变换后仍逐单元相同，所以引入新的原 CrossEq。
不同新行可以使用不同内部 token 表、宽度、地址与 boundary；
原邻接正是比较各自行参数指向的状态片段，没有要求内部表整数相同。

PA 对已收集的行数 i≤k 作归纳，维护每行 G、相应续延关系及所有 j+1<i 的接缝。
新增行后选更大外层宽 U_(i+1)≥U_i，使用 V_(i+1)=2^U_(i+1)，
把旧声明单元重包后追加 429 个新数。全部单元<新值界，旧 Read 不变，
新接缝由前段构造给出。因此得到同一张外层表中的完整 k 行，
没有使用无限选择，也没有要求所有内层见证具有多项式位长。

源初态为 (P,C,[Parse],[],running)，源末态为 ([],[],[],[(Gamma,1)],running)。
新片段准确从 (P++R,C++S,[Parse]++K0,V0,running) 到
(R,S,K0,[(Gamma,1)]++V0,running)。它只是一段子运行，通常不是新的接受矩阵。
若源结论集为 {f}，末端保留同一 Gamma 及其可能的重复项。

另外，新 MP 不必使用外部势函数来估计这两条源片段的行数。
设源 AcceptedPayloadMatrix 的 inputTokenCount 为 M_I、M_A，
其真实 fuel 为 F_I=4M_I+12、F_A=4M_A+12，前缀长度满足 k_I<F_I、k_A<F_A。
若五个新增节点按原 G 构造成功，它们需要 9 行，再加最终 Finish 一行，故

`L=k_I+k_A+10≤F_I+F_A+8`。

新规范流若按构造有 M_out=M_I+M_A+H，仅五个 proof 标签就给 H≥5。于是

`F_out=F_I+F_A+4H-12≥F_I+F_A+8≥L`。

剩余 F_out-L 行用原接受吸收引理补齐；等号情形补零行。
这是以新节点真实拼接为前提的燃料算术结论，不替代新节点的图构造。
完整归纳及其独立复核见 [原 G 的子运行片段](../docs/paper_direct_segment_transport_20260905_zh.md)。
输入公共公式的内部长度来源在下一节补齐。剩余关键接口为新节点 parser/规则
见证，以及输出 canonical 编码、初态与结论的同一关系。

### 5.13 原公共公式的来源与 inputWidth 内部界

这里从原接受矩阵证明长度界，不调用树解码或标准模型下的 verifier 正确性。
记 inputWidth=W、inputTokenCount=M，公开公式的原 formulaWidth=wf、
formulaTokenCount=L。由 InitialEnvironment，第一行只有一个全空 Parse 任务。

若首次 parse 为叶，TaskDrop(1) 后任务栈为空，下一步只能 Finish，故 k=1；
叶的实际 Gamma 桥给最终结果 Gamma 与首次根 Gamma 逐项相同。
若首次 parse 为非叶，one/two schedule 在栈底留下根 combine，
其完整字段经 TaskCrossTableBridge 与首次根对齐，且 tag≠10。

对边界状态 s_1,…,s_(k-1) 跟踪栈底这一索引。任务数 t>1 时，
Drop(1) 将标记从 t-1 移到 t-2；ReplaceHead 的 t+p=t'+1 将其移到 t'-1。
原尾部全称及 TaskCore 字段刚性保持根 Gamma。
标记成为唯一任务时，只能 combine；弹出后任务栈空，下一步只能 Finish。
最终 s_k 任务栈为空，因此标记恰在最后一个前缀行弹出。
该 combine 的 PushDrop HeadEq 使用当前 task Gamma，所以最终唯一结果的
Gamma 与首次根逐项同值、计数相等。此标记归纳已按原行关系独立复核。

原 AcceptedConclusionRow 允许重复项，但给 GammaCount>0 且每项等于公共公式。
取第 0 项并沿前段拉回根。五个原 ProofRoot endpoint 都先有
P=rootTag::Q，其 Sequent endpoint 又给 Q=GammaCount::U。
由于 Gamma 非空，实际 SequentTrace 的第 0 行存在；其 AppendSlices 直接给
U=Gamma0正文++nextSuffix。因此在原 proof 流中

`2+L≤proofCount`，`F[j]=P[2+j]（j<L）`。

这里去掉的是 proofTag 和 sequent 的计数，不是内部存储额外加入的列表长度头。
这条前缀关系由 Cons、Append 及边界 Entry 唯一性直接取得，不需先验证公式语法。
再沿初始流和 InputSplit 的两层 CrossEq，将 P[j] 识别为原 inputTable 的第 j 行。

输入和公开公式都使用原 CanonicalAtWidth。令其 offset 读数分别为 a_i、b_j，
原端点给 a_0=b_0=0、a_M=W、b_L=wf；TokenSegment 给

`a_(i+1)=a_i+2ell(input[i])+2`，
`b_(j+1)=b_j+2ell(F[j])+2`。

由 F[j]=input[2+j]，PA 对 j≤L 归纳得到 a_(2+j)=a_2+b_j。
又 a_2≥4、a_i 单调、2+L≤M，故

`wf+4≤a_(2+L)≤W≤bound`。

公式原 sentinel 等式 f=payload+2^wf、payload<2^wf 又给 ell(f)=wf+1。
从而消去矩阵见证得到固定 PA 结论

`P_direct(bound,f) → ell(f)≤bound+1`。

特别，MP 的两份公共公式载荷本身≤n；I=NOT A OR B 的准确 raw token 拼接
使 B 的载荷≤I 的载荷，才可把第 5.1 节的 a、b 收束为≤n。
下一节构造新节点的普通语法基础图和两条精确否定图；九个新增 G 行仍需接合。
完整标记、重复项处理与拼接顺序见
[MP 组装审计](../docs/paper_direct_mp_assembly_audit_20260905_zh.md)，
同一原表及 offset 的逐项推导见
[公式来源与位宽证明](../docs/paper_direct_formula_provenance_20260905_zh.md)。

### 5.14 新公式的普通解析图与精确否定图

续延定理只能搬运已有图，新节点还需要从其明确公式编码构造基础图。
这里用有限后序节点表表达当前算术语法：每个节点记录项/公式类别、tag、binder、
符号码、较小的子节点索引，以及与子节点的 raw token 拼接等式。
函数合法对为 (0,0)、(0,1)、(2,0)、(2,1)，关系合法对为 (2,0)、(2,1)，
均逐个选择原固定符号码图的数值析取。

PA 对节点索引作加强归纳：目标项或公式的编码位于输入前缀，后接任意 R，
头任务为 (kind,d,0)，后接任意 K；构造原 Syntax 行将该前缀消费完，
剩下 (R,K,running)。Repeat(d,a) 用对 a 的归纳，逐项生成项任务后再处理余项。
它的步数为 1+sum(1+s_i)，包含最后一次零 Repeat，不能漏算调度。

变量一步消费 2 个 token；函数和原子先消费 3 个，再执行 Repeat；
常量公式消费 1 个，二元公式依次处理左、右任务，量词把 binder 加 1 后处理子式。
这些事件对应原 Term/Formula/Repeat 的明确活动子式，七个槽放原 binder、
tail boundary、长度与 tag/参数/符号码。逐项规范端点提供 At、Drop、Cons 和 SameRows。
对相同节点表归纳给真实事件数 s≤2L-1，L 是 raw token 数。

取 K=[] 后加一次 Empty，得到 completed(R)，总步数≤2L；
再用原 Done_completed 补到 f=16(L+|R|+1)^2+8。
先排列 f+1 个原始状态块与相容背景，确定最终 N，再以 N 重包所有 boundary。
选单元宽 u 容纳原始 token，取 H=1+u+(N+1)N、V=2^H，
所有状态坐标、七个槽和 status 见证均在原界内。
依次给每步原 27 个存在量及两个 StatusValid，给初末原 23 个存在量，
最后给完整 Endpoint 的十个坐标，得到原 SyntaxExactEndpointGraph。
这是一份 PA 归纳构造，未从 Nat parser 的成功等式反推算术图。
详见 [普通语法基础图](../docs/paper_direct_syntax_base_graph_20260905_zh.md)。

mode=3 的否定图复用同一事件数组，并附加累积输出 Z。
Term 行用原 AppendSourcePrefix 复制所消费头；Formula 行将头按

`0↔1，2↔3，4↔5，6↔7`

替换，消费头中的其余 token 保持，选择原 AppendMappedSourcePrefix。
原 NegationTagGraph 的四个 pair 见证依次为 0、1、2、3。
Repeat、Empty、Done 通过原 OutputSameRows 保持 Z。
对语法节点归纳，项输出不变，公式输出恰为当前系统的否定正规形；
不是加入一个新的单目 NOT 标签。

每条 TransformState 重新写为 parser 状态后接独立的带头输出列表。
completed [] 的 [1,1,0] 是 parser 的空后缀，后面仍有累计输出的长度头，
两个列表不能混同。确定同一背景和最终 N 后，重新计算各槽及 boundary，
填原每步 37 个存在量，并补 current/next 的 StatusValidBounded。
取 H=N(N+1)+w+1、V=2^H，满足原 TotalTrace 的面积界。
末态为 completed []、累计输出为指定否定；原 EmptyFinal 的三项规范见证成立，
三个 reservedOutput 取 0，因此给真正的 TotalExactBoundedGraph 成功输出分支。

八种公式头置换是对合，项编码保持。逐构造器归纳给同一 raw 编码上的

`Neg(Neg(A))=A`，
`Neg([5]++Neg(A)++B)=[4]++A++Neg(B)`。

因此两次基础构造分别给 Closed 所需的 B→NOT B 图、Cut 所需的 I→NOT I 图，
且第二个输出准确是 A AND NOT B 的编码，可以连接 And 的构造成员检查。
输出 token 个数与输入相同；只有原子头 0/1 的 binaryNat 位长可能变化，
所以载荷满足 Weight(Neg(A))≤2Weight(A)，不能把两种长度混淆。
完整逐输出图、共享槽和末态证明见
[精确否定基础图](../docs/paper_direct_negation_base_graph_20260905_zh.md)。
两个基础稿已相互核对事件、步数、布局和槽接口；新外层 G 的合成与 p3 短证明
计量仍须分别完成，条件 (3) 尚未在本节宣告结束。

## 6. 向上单调版本的条件下界证明

本节给出条件定理的完整推导，以区分“下界证明的数学逻辑”与“当前谓词满足前提”。
原 Pudlak 论文印刷页 172–174 是相关固定点论证，页 177–179 讨论自然证明谓词。
原文所印条件 (0) 的方向与本稿采用的向上单调性不一致；这里明确重新证明本稿版本，
不把这一差异直接认定为已有正式勘误。[Pudlak 原文](https://users.math.cas.cz/~pudlak/fin-con.pdf)。

### 6.1 条件定理的全部输入

固定一致且包含 Q 的理论 A 及其证明系统，使用同一长度度量。令 ell(m)=ceil(log2(m+1))。
以下每一项都是本节的前提，不能由标准模型语义等价自动替代。

- 向上单调性：A 有固定证明说明 u≤v 且 P(u,f) 蕴含 P(v,f)。
- 条件 (1)：若 A 有长度不超过 a 的 phi 证明，则 A 有长度不超过 p1(a) 的
  P(a,code(phi)) 证明。
- 条件 (2)：A 有长度不超过 p2(ell(a),ell(f)) 的证明说明
  P(a,f) 蕴含 P(q1(a),code(P(a,f)))。
- 条件 (3)：A 有长度不超过 p3(ell(a),size(phi),size(psi)) 的证明说明
  P(a,code(phi)) AND P(a,code(phi IMPLIES psi)) 蕴含 P(q2(a),code(psi))。
- 编码性质：上述闭实例、固定逻辑模板、短数词、公式码和代入具有关于相应输入
  位数的固定多项式长度界；固定多项式数值的计算以及真数词比较可在 A 内短证明。
- 高效固定点：存在 D_m，并记 S_m=P(m,code(D_m))，使 D_m、S_m 及其代码位数
  关于 ell(m) 多项式有界，且 D_m IFF NOT S_m 有 poly(ell(m)) 长度的 A 证明。
- 固定次数证明组合有固定多项式成本。特别地，最后一次 MP 的输出长度允许由
  D*(L+H+1)^J 控制，D≥1、J≥1 固定，而不要求其成本线性。

p1、p2、p3、q1、q2 均为固定多项式。用非负整数系数多项式支配 q1、q2，
再通过向上单调性抬高内部界，可以假设二者非负且处处不小于 a+1。
所有“短”都指本节固定度量，不混入另一系统的行数或抽象长度。

### 6.1a 当前直接谓词的条件 (0)：纸面闭合

这一项可以从实际公式直接证明，不需要先把其余运行轨迹内部化。
`integration/FoundationCompactNumericListedDirectProofPredicate.lean` 的
`compactNumericListedDirectPredicateMatrixDef` 中，公共 bound 参数只出现于首个合取
`inputWidth≤bound`；后面的接受载荷矩阵、公式表格、结论行均不含这个公共参数。
最外层 `compactListedPADirectProofFormula` 恰有 20 个无界存在见证。

因此把这 20 个变量记作 w，把其中 inputWidth 记作 width(w)，就有同一公式的语法展开

```text
P(b,f) = EXISTS w [width(w)≤b AND R(w,f)]，
```

其中 R 不含 b。这里是对既有对象公式的展开，不是从标准模型语义推测的等价。

在 PA 内，假设 b≤b' 且 P(b,f)。对 20 个存在量词逐次消去，保留新鲜变量 w，
得到 width(w)≤b 和 R(w,f)。用 PA 的序传递推出 width(w)≤b'；
R(w,f) 逐字保留。引入合取，再以原来同一组 w 引回 20 个存在量词，得到 P(b',f)。
消去外部假设并全称推广，得到固定 PA 定理

```text
FORALL b,b',f: (b≤b' AND P(b,f)) IMPLIES P(b',f)。
```

所有见证变量均可预先改名，使存在量词消去的特征变量条件成立。
20 层是固定常数，R 是固定公式，故上述推导是一份固定有限 PA 证明。
以短二进制数词实例化 b、b'、f 时，只有固定多个替换位置，
闭实例长度因此可由这些数词长度的固定多项式控制。
这完成了向上单调性的纸面证明；本轮没有生成对应 Lean 证明或编译通过声明。
条件 (1)、(2)、(3) 不因此自动成立。

### 6.1b 当前 compact 闭公式码的高效固定点：纸面构造

必须先处理一个实际编码差异：现有参数化对角化文件给出
`theta(m) IFF predicate(FoundationCode(theta),m)`，其中右端是固定的 Foundation
开公式码。所需结论却必须使用当前闭实例的 compactFormulaCode(D_m)。
因此不能直接拿旧定理的固定开式码代入 P_direct。

下面保留 P_direct，单独定义一个有限代入机。令 nu(a) 为当前二进制短数词；
openCode(B) 对二参数开式 B 使用当前 binaryFormulaCode 并添加同一 sentinel，
闭公式上它恰是 compactFormulaCode。

**具体代入程序 SUB(x,u,v)。** 先从 x 去除 sentinel、按当前二进制 token 编码
读取一个二参数算术开式；不合法则输出 0。用前缀语法栈携带量词深度 h：
变量号小于 h 时保留，号为 h 时输出 nu(u)，号为 h+1 时输出 nu(v)，其余拒绝；
量词子任务把 h 增加 1；关系、函数和连接词头按原次序保留。
语言的函数、关系元数来自固定有限表，非法大元数不能触发按其数值长短的循环。
正好消费整个输入后对输出位串添加 sentinel。

按项和公式结构归纳，在量词处保留新绑定变量，得

```text
SUB(openCode(B),u,v)=compactFormulaCode(B[nu(u),nu(v)])。       (6.2)
```

输入总位数 s=1+ell(x)+ell(u)+ell(v)。每个输入节点只访问一次，每个参数位置
至多输出 O(s) 位，故输出长度 O(s^2)。有限栈逐位实现这些扫描、比较和追加，
时间 T 及每个配置坐标位数 w≥1 都可由固定多项式 Q(s) 控制。

**辅助算术关系及唯一性。** 把这个确定性有限栈程序的字母表固定为基数 k，
push 和 pop 由 `r'=k*r+a` 或 `r=k*r'+a` 表示，1≤a<k 的合法字母集合固定。
控制状态分支互斥；初配置由 x,u,v 决定，终止状态吸收。
所以其一步 Step 是含固定多个闭加乘序原子的有限分支关系。

用固定坐标数 r 的 beta 商余表记录运行，定义

```text
Beta(B,C,i,a) := a<1+(i+1)C AND
                EXISTS q≤B: B=q*(1+(i+1)C)+a。
```

S(x,u,v,z) 表示存在长度 T、C≥1 和 r 个表格数，首行是指定初配置，
末行终止且输出为 z，并且每个 i<T 的相邻两行满足 Step。
它是原算术语言中的固定公式，外层存在量词及局部检查均明确；不含 P_direct。

PA 的商余唯一性使每个表格行的值唯一。按 Step 的有限互斥分支证明后继唯一；
再对两份运行的公共时间索引作 PA 归纳，使两份配置逐行相等。
一份先终止时，吸收分支使另一份剩余运行保持同一输出。由此得到固定 PA 证明

```text
S(x,u,v,z) AND S(x,u,v,z') IMPLIES z=z'。                     (6.3)
```

这不要求 PA 已证明该程序在任意输入上终止，也不是从程序接受推出 PA 公式为真。

**短运行的完整载荷。** 给定实际 T 步运行，最大配置数为 M，取
`C=(T+1)!*(M+1)`，模数 d_i=1+(i+1)C，0≤i≤T。
它们两两互素：公因子与 C 互素、整除 (j-i)C，故整除 j-i；而 j-i 也整除 C。
扩展欧几里得和逐项中国剩余构造每个表格 B_j，使第 i 行余数为真实坐标。
取 B_j 小于模数乘积，得到

```text
ell(C)=O(w+T log(T+2))，
ell(B_j)=O((T+1)*(w+T log(T+2)))。
```

核验这些具体表不需要在 PA 内重演整个中国剩余存在性证明：每个行和 Step
直接给出真实商余、配置数及分支，以第 4.3 节的闭原子编译构造短证明。
所有数词位宽受上述多项式控制。

全称遍历也明确计长。对固定局部公式 Q(i,b)，令 H(t,b)=FORALL i<t:Q(i,b)。
PA 有固定证明 H(0,b) 及
`H(t,b) AND Q(t,b) IMPLIES H(t+1,b)`：把 i<t+1 分为 i<t 和 i=t 两种即可。
逐个用短数词实例化 t=0,…,T-1，配合二进制加法，把 nu(t)+1 改写为 nu(t+1)。
每次合取和 MP 只保留已有 H(t,b) 的证明一次，所以 T 次的成本相加。
再加入首末条件及固定多个表格存在见证，得到

```text
S(nu(x),nu(u),nu(v),nu(SUB(x,u,v)))
具有完整载荷 poly(s) 的 PA 证明。                           (6.4)
```

**自代入。** 先固定上述 S 的全部展开式，再定义

```text
Psi(x,m)=FORALL z: S(x,x,m,z) IMPLIES NOT P_direct(m,z)，
e=openCode(Psi)，D_m=Psi[nu(e),nu(m)]，c_m=compactFormulaCode(D_m)。
```

这先定义有限语法，再计算其开式码，最后做闭代入，没有要求解一个数值自递归方程。
由 (6.2)，SUB(e,e,m)=c_m；e 固定，所以 (6.4) 产生
`S(nu(e),nu(e),nu(m),nu(c_m))` 的 poly(ell(m)+1) 完整载荷证明。

D_m 配合这份运行证明给出 NOT P_direct(m,c_m)。反方向，若 NOT P_direct(m,c_m)，
任取满足 S(e,e,m,z) 的 z，由 (6.3) 和已证运行实例得 z=c_m；等式代换及全称引入
得到 D_m。固定次数组合保持多项式成本。因此

```text
PA 有 D_m IFF NOT P_direct(m,compactFormulaCode(D_m)) 的证明，
完整 proof+certificate 载荷为 poly(ell(m)+1)。                 (6.5)
```

Psi 固定且 nu(m) 只在固定多个位置出现，|D_m|=O(ell(m)+1)，
ell(c_m)=|D_m|+1；P_direct(m,c_m) 的公式和代码位数同样线性有界。
这完成同一 P_direct 高效固定点的纸面构造。
完整算法、符号展开与载荷证明见 [固定点构造](../docs/paper_direct_fixed_point_20260905_zh.md)，
已经过独立复核。新辅助代入程序的完整指令表及这些 PA 推导尚未写入 Lean；
纸面算法实现不应被称为旧参数化文件已经形式化的结论。

### 6.1c 确认 (1) 与再确认 (2) 的不同成本要求

对完整载荷 W≤a 的已接受证明，第 5.5 节给出宏步数 F≤2W+12。
但每个宏步包含 429 列及内部语法、公理、公式变换轨迹，不能只按宏步数收费。
实际语法、证明树、证书解析器的燃料分别为
16*(L+1)^2+8、32*(L+1)^2+16、16*(L+1)^2+8，L 是 token 个数。
当前公开列的位数界尚未覆盖这些内部轨迹的每个控制量。

可以先证明一条明确的核验成本引理。对固定原矩阵，选择正确析取支和存在见证，
将有界全称按原数值界展开，调用原闭算术和位原语的短证明编译器。
若这份证书中的所有全称数值界、位索引及数值项/存在见证的位数都≤B，
固定量词深度 d 至多产生 O((B+1)^d) 次局部调用。
全称前缀 H(k)=FORALL i<k:Q(i) 用固定模板
H(k) AND Q(k) IMPLIES H(k+1) 逐次推进，每次只保留旧证明一次；
总成本是各 Q(k) 证明成本之和加 K 次固定多项式开销。
故完整 proof+certificate 载荷为 K*(B+1)^e，K、e 只依赖原矩阵和编译器。

原位关系可以用商余式短核验：

```text
bit(v,i)=1 IFF EXISTS k≥0, 0≤r<2^i: v=k*2^(i+1)+2^i+r；
bit(v,i)=0 IFF EXISTS k≥0, 0≤r<2^i: v=k*2^(i+1)+r。
```

这里商 k 没有 r 的余数界。原 expDef 的短证明成本关于指数 i 的数值多项式，
所以必须控制 i≤B，不能只给 ell(i)≤B。
公理闭包图中的 targetCount=depth+bodyCount 还直接给 depth≤targetCount，
可按实际目标列表长度为闭包全称计费，而不把它视为一个只控制位数的大循环。

条件 (1) 仍须为同一 P_direct 的所有活跃内部图建立 B=poly(a) 的完整账本，
再将上述生成器引回原来的 20 个存在量词。
现有 compileSigmaOneTruth 端点只保证从真值得到证明，没有给出所需成本界。

条件 (2) 要求的是 poly(ell(a),ell(f)) 长度的蕴含证明。
先运行成本 poly(a) 的 (1) 生成器，再把成本称为 poly(log a)，不能证明 (2)。
需要一份统一的 PA 内生成器正确性及输出长度定理，随后作短数词实例化。
第 5.13 节已在原矩阵中证明公共公式来自原载荷及其位宽界。
仍须处理任意输入见证的规范化，不能把可能很大的旧辅助表直接放进短输出。
因此本节没有将 (1) 或 (2) 宣布完成。
实际定义、量词预算及来源逐项列在
[确认与再确认报告](../docs/paper_direct_confirmation_20260905_zh.md)。

### 6.2 固定点没有长度不超过 m 的证明

若 D_m 有长度不超过 m 的证明，条件 (1) 给出 S_m 的 A 证明。
同一 D_m 证明与固定点正向蕴含给出 NOT S_m 的证明。这与 A 一致矛盾。
所以对每个 m，D_m 没有长度不超过 m 的证明。
这里只在元理论中使用一致性，没有把一致性加入 A 的公理。

### 6.3 内部确认必须使用真实短长度

固定点正向蕴含 D_m IMPLIES NOT S_m 有长度至多
`t(m)=E*(ell(m)+1)^e` 的证明，E、e 固定。充分大的 m 上 t(m)≤m。
先在真实短长度 t(m) 处用条件 (1)，获得
P(t(m),code(D_m IMPLIES NOT S_m))，其证明长度 p1(t(m)) 仍是 poly(ell(m))。
再用内部单调性和短数词比较 t(m)≤m，获得
P(m,code(D_m IMPLIES NOT S_m))。

对固定逻辑模板 S_m IMPLIES (NOT S_m IMPLIES falsum) 同样处理。
不能直接在 m 处用条件 (1) 后，把得到的 p1(m) 错记为 poly(log m)。

### 6.4 在固定多项式界内形成矛盾的内部证明

条件 (2) 给出

```text
S_m IMPLIES P(q1(m),code(S_m))。
```

条件 (3) 结合 6.3 的内部确认，给出

```text
S_m IMPLIES P(q2(m),code(NOT S_m))。
```

定义固定多项式

```text
h(m) = m+q1(m)+q2(m)+1
k(m) = h(m)+q2(h(m))+1
r(m) = k(m)+q2(k(m))+1。
```

在 S_m 假设下，将 S_m 和 NOT S_m 的内部证明界抬高到 h(m)；
将 6.3 中恒真式的内部证明界也抬高到 h(m)。先用条件 (3) 得到
P(q2(h(m)),code(NOT S_m IMPLIES falsum))。
再将其界及 NOT S_m 的内部界抬高到 k(m)，第二次用条件 (3)，得到
P(q2(k(m)),code(falsum))。最后抬高到 r(m)，形成

```text
S_m IMPLIES P(r(m),code(falsum))。                (6.1)
```

所有内部数值是 m 的固定多项式，数词位数 O(ell(m))；相关公式及其代码位数
为 poly(ell(m))。条件 (2)、(3) 的外部证明成本按这些位数计量。
组合次数固定，所以 (6.1) 的实际 A 证明长度为 poly(ell(m))。
这里严格区分内部所声称的证明界 r(m) 与 (6.1) 自身的外部证明长度。

### 6.5 有限一致性蕴含固定点

记 F_b=NOT P(b,code(falsum))。对 (6.1) 取逆否命题，再接固定点反向蕴含，
得到 F_r(m) IMPLIES D_m 的 poly(ell(m)) 长度证明。
若 b≥r(m)，向上单调性给出 F_b IMPLIES F_r(m)，
故 F_b IMPLIES D_m 的证明长度受 poly(ell(b)+ell(m)) 控制。

### 6.6 一般多项式组合成本仍给出正幂下界

取整数 C、K≥1，使 r(m)≤C*(m+1)^K。给定充分大的整数 b，令

```text
x=(b/C)^(1/K)，m=floor(x)−1，eta=1/(2*C^(1/K))。
```

当 x≥4 时，r(m)≤b，且 m≥x−2≥x/2=eta*b^(1/K)，又 m≤b。
将 6.5 的蕴含证明长度、所用公式长度统一支配为
H_b≤A0*(ell(b)+1)^v，A0≥1、v 为非负整数。
若 F_b 有长度 L 的证明，最后一次 MP 将产生长度不超过
D*(L+H_b+1)^J 的 D_m 证明。

取 epsilon=1/(4KJ)>0。充分大的 b 上 H_b≤b^epsilon。
若 L≤b^epsilon，则输出长度不超过

```text
D*(3b^epsilon)^J = D*3^J*b^(1/(4K)) ≤ eta*b^(1/K) ≤ m。
```

这与 6.2 矛盾。因此充分大的 b 上，F_b 没有长度不超过 b^epsilon 的证明。

可显式控制这里的阈值。令 m0 保证 6.3–6.5 的短模板界均适用，并取

```text
T = ceil(max(1, A0*4^v*(v+1)!*(2/epsilon)^(v+1)))
B_log = 2^T
B0 = ceil(max(1, C*(m0+2)^K, C*4^K, B_log,
              (D*3^J/eta)^(4K/3)))。
```

核查对数项：令 t=floor(log2 b)≥T≥1，则 ell(b)+1≤4t。
利用 log 2≥1/2 和指数函数的第 v+1 项，
2^(epsilon*t)≥(epsilon*t/2)^(v+1)/(v+1)!≥A0*4^v*t^v。
所以 H_b≤b^epsilon；B0 的其余项分别保证 m≥m0、x≥4 及最后的幂比较。
这些是条件数据给定后的阈值表达式；当前项目尚未给出全部条件数据，不能声称已提取数值 B0。

### 6.7 重标定与对撞的最后算术

取 d=4KJ，则 d*epsilon=1。令 G_n=F_rho_d(n)。当 rho_d(n)≥B0 时，

```text
G_n 没有长度不超过 rho_d(n)^epsilon = (n+1)^n 的证明。
```

可取 N_low=max(1,ceil(log2(max(1,B0))))，因为 n≥1 时 rho_d(n)≥2^n。
若将来上界桥真正对同一 G_n 给出 minProof(G_n)≤C_u*(n+1)^k，
并给出实际证明（从而此处的最短长度确实存在），
其中 C_u≥1、k 非负整数、n≥N_upper，则取
n≥max(N_low,N_upper,k+1,ceil(C_u))，即有

```text
C_u*(n+1)^k < (n+1)^n < minProof(G_n)，
```

矛盾。本节补齐了条件下界、重标定和对撞的推导，
没有补齐当前 P 的前提实例化，也没有提供所需 Sondow 上界桥。

## 7. 对关键桥的数学归约与反射障碍

第 3 节给出真实的有限证书 C(p,q,n)，以及有理性下的统一成功证明。
其检查的仍是特定对数表达式的有理区间，而 G_n 要排除长度界内的全部 PA 矛盾证明。
本节把两者之间的任务进一步精确化，没有预设实际归约存在。

### 7.1 短蕴含族承载的完整难度

固定整数 p、正整数 q。本节出现于 PA 公式中的 C_n 一律指第 4.3 节选定的
规范闭源句 Phi_(p,q,n)，不是尚未展开的运行谓词。
其标准真值与第 3 节有限算法 C(p,q,n) 的接受性等价。
第 4.3–4.4 节已给出所选源句的真、假两侧短证明构造及源、目标的公式大小界，
第 5 节的组合计量保证固定逻辑组合的完整载荷成本为多项式。
因此以下定理仍以第 6 节同一 G_n 的下界为条件，
但不再把这一个具体源句的双向算术编译作为额外未证字段。
若另换为含任意轨迹存在量词的源公式，则必须重新证明必要的 PA 内等价和长度界。

**条件定理 7.1。** 在第 6 节下界成立时，对上述具体源句，以下两项等价：

1. gamma≠p/q；
2. 存在常数 C、k、N，使每个 n≥N 上 C_n IMPLIES G_n 有完整载荷
   不超过 C*(n+1)^k 的 PA 证明。

证明：若 gamma≠p/q，第 3.5 节说明 C_n 只在有界多个 n 上接受，故最终拒绝。
由假计算轨迹的短证明转换，得到 NOT C_n 的短 PA 证明。
实例化经典恒真式 NOT C_n IMPLIES (C_n IMPLIES G_n)，即得第 2 项。

反之，若第 2 项成立且 gamma=p/q，第 3.4 节保证最终全部接受。
由真计算轨迹的短证明转换，得到 C_n 的短证明；与第 2 项的蕴含作 MP，
得到 G_n 的多项式短证明，与第 6 节下界矛盾。所以 gamma≠p/q。证毕。

量词中的 p、q 固定；常数和阈值可以依赖它们。这个定理说明，
在所列条件下，短蕴含族并不是比排除该有理数更弱的常规接线任务。
它不证明任何独立归约必然循环：独立构造这种蕴含族，确实会给出新的排除证明。
用“蕴含族存在”作为未经证明的输入，则没有降低目标的数学难度。

### 7.2 尝试有限可靠性时，缺口恰好落在反射实例

设 b=rho_d(n)。由第 6 节的定量内部化条件，可以先在 PA 内短证明

```text
P(b,code(falsum)) IMPLIES P(h(b),code(NOT C_n))，      (7.1)
```

其中 h 是固定多项式。构造如下：对恒真式 falsum IMPLIES NOT C_n
先用其真实 poly(n) 证明长度做条件 (1) 的内部确认，
充分大的 n 时将内部长度界抬高到 b，再应用一次内部 MP。
这里 log b=O(n log(n+1))，且 C_n 的公式长度为 poly(n)，
所以 (7.1) 自身的 PA 证明长度仍是 poly(n)。

(7.1) 只说明存在 NOT C_n 的证明。要推出 NOT C_n，还需要另一条 PA 推导：

```text
RF_n: P(h(b),code(NOT C_n)) IMPLIES NOT C_n。          (7.2)
```

将 (7.1)、(7.2) 合成并取逆否命题，就得到 C_n IMPLIES G_n。
所以“从任何短矛盾证明导出源证书不成立”的方案，
不能跳过 (7.2)。局部语法检查器的正确性没有提供这条内部反射。

还可定位其长度困难。以下固定 n 不小于 (7.1) 构造和第 6 节下界的共同尾部阈值。
假设 n 是真正接受的实例，源 C_n 已有多项式长度证明；
若 (7.2) 有长度 r_n 的证明，则组合后 G_n 的证明长度至多

```text
A*(r_n+P0(n)+1)^J，
```

其中 A≥1、J≥1 固定，P0 是固定多项式。由第 6 节下界，必须有

```text
r_n > A^(−1/J)*(n+1)^(n/J) − P0(n) − 1。
```

充分大的接受实例上，任一此类反射证明因此至少具有
`[1/(2*A^(1/J))]*(n+1)^(n/J)` 的长度。
这里没有断言实际存在无界接受实例，也没有假设反射证明一定存在；
这是对接受实例上任何已有反射证明的条件长度约束。

### 7.3 显式枚举和更强理论两条方案的具体代价

若算法枚举长度不超过 b 的全部二进制载荷，并把每个拒绝记录逐项放入证书，
就至少处理 2^(b+1)−1 个字符串。每项占至少一位时，其输出列表长度也至少这么大。
代入 b=rho_d(n)，这个完整列表方案的输出不可能关于 n 多项式有界。

这只排除逐项保留记录的方案。指数运行时间本身不能证明所有输出证明都长；
若改成用归纳压缩整个枚举，需要独立证明压缩后的 PA 推导及其长度界。

若改在 PA 加一致性公理中证明 G_n，则使用了另一个理论。
要把所得短证明用于当前 PA 下界，仍需将其转换为同一 PA 的短证明。
如果这种转换对所有 G_n 都多项式可行，便直接与第 6 节下界相撞，甚至不需要 Sondow。
保留该额外假设所证明的 Con(PA) IMPLIES G_n，不是 G_n 的无条件 PA 证明。

### 7.4 对数接近整数：通用分离估计不足，必须使用特殊结构

检验直接数论反证候选。假设 gamma=p/q，n≥ceil(q/2) 时 q 整除 D_n，故

```text
m_n=T_n-(D_n/q)B_n*p 是整数，
Y_n=log S_n-m_n=D_n I_n，
a_n≤Y_n<2^(-n)。
```

只证明 log S_n 不是整数没有推进：积分正性早已给出 Y_n>0。
需要一个与 2^(-n) 上界不相容的新估计。

已核对的 Mahler 定理给出：充分大整数 f 对任意整数 a 满足
`|log f-a|>exp(-40 log f log log f)`。
直接取 f=S_n、a=m_n 即满足适用条件。
来源：[Mahler 原文，第 397 页 Theorem 7](https://carmamaths.org/resources/mahler/docs/118.pdf)。

但本稿的真实高度界是

```text
(log 2)*4^n/[2(n+1)^2] ≤ log S_n
                       ≤ 2(n+1)^3*36^n*log(2n)。
```

所以代入所得下界 exp(-40 log S_n log log S_n) 关于 n 双指数小，
最终甚至小于已证明的 a_n=(9/256)^n/64。压缩指数列表不改变 S_n 的代数高度，
不能用列表位数代替 log S_n。指数侧分离估计有同一障碍；
完整代参见 [整数对数分离核查](../docs/paper_log_integer_separation_20260905_zh.md)。

还可给出不依赖外部定理的精确兼容性例子。令

```text
M_n=4^n，epsilon_n=(D_n/2)*16^(-n)，
S*_n=floor(exp(M_n+epsilon_n))+1，r_n=log S*_n-M_n。
```

用 x<floor(x)+1≤x+1 及 log(1+t)<t 得

```text
epsilon_n<r_n<epsilon_n+exp(-M_n-epsilon_n)<2*epsilon_n。
```

最后一步因为 4^n≥4n>n log16，且 D_n≥2 使 epsilon_n≥16^(-n)。
对同一个 D_n 定义 I*_n=r_n/D_n，便同时有

```text
(1/2)*16^(-n)<I*_n<16^(-n)，
a_n<I*_n，a_n<D_n I*_n<D_n*16^(-n)<2^(-n)，
log S*_n-M_n=D_n I*_n，M_n 为整数。
```

其中 a_n/[(1/2)*16^(-n)]=(9/16)^n/32<1，故连第 3.1 节的积分下界也保留。
而 log S*_n=4^n+O(2^(-n))，完整整数的高度也处于同样的双指数层级。
因此整数性、粗高度、正余项和这些余项上下界本身是相容的；它们不能单独推出矛盾。
S*_n 不是 Sondow 的幂积，I*_n 也不是原积分，故这个例子不否定利用其特殊结构的证明。
它明确说明必须在新推导中实际使用精确幂积或积分结构，不能只保留它们的数值界。

纯对数线性形式的另一注意点是：写成 `sum e_k log(n+k)-m_n` 后，不能将整数项
伪装为 m_n log(e) 再套所有底数均须代数的定理。该底数 e 不满足代数性前提。
此处没有把任何通用超越估计当作已完成的关键桥。

### 7.5 特殊质数对数消元：已证短向量与未证有效方向

这次直接使用原 Sondow 幂积。固定 n，取 k=n,…,2n，令

```text
Q_k=D_k B_k，R_k=D_k I_k，E_(p,k)=v_p(S_k)，p≤4n 为质数。
```

矩阵 E 的列数 m=n+1，行数 r=pi(4n)=O(n/log n)。原恒等式给

```text
sum_p E_(p,k)*log p = T_k−Q_k*gamma+R_k，0<R_k<2^(-k)。
```

对整数向量 a∈ker E，设 u(a)=sum a_k Q_k、v(a)=sum a_k T_k、
r(a)=sum a_k R_k，则精确消元得到

```text
r(a)=gamma*u(a)−v(a)。
```

原同底数指数界给 0≤E_(p,k)≤H_n=8n(2n+1)^3*36^(2n)，log H_n=O(n)。
这里所需质数数目上界可初等推出：theta(2t)−theta(t)≤log binom(2t,t)≤2t log2，
在二次幂上相加得 theta(x)<4x log2；按 sqrt(x) 分割质数后，
pi(x)≤sqrt(x)+2theta(x)/log x=O(x/log x)。

充分大的 n 上 r<m。令 A=floor((mH_n+1)^(r/(m−r)))+1，
将整数立方体 {0,…,A}^m 映为 E x。
像数≤(mH_n A+1)^r≤((mH_n+1)A)^r<(A+1)^m，
故有不同 x、y 同像。取 a=x−y，得到

```text
a≠0，E a=0，||a||∞≤A，log A=O(n/log n)=o(n)，
|r(a)|<2A*2^(-n) -> 0。
```

这一短整数关系已经证明，但 a≠0 不保证 r(a)≠0。
公共核 ker(E,Q,T) 中的非零向量余项恒为 0，而且真实 Sondow 矩阵中
无条件存在同一量级的这种短向量。确实，Q_k<32^k，
T_k≤2k Q_k≤4n*32^(2n)≤H_n；把 Q、T 两行加入 E 后，
行数仅从 r 变为 r+2，充分大 n 上仍小于 m。
同一鸽巢构造给出非零 a∈ker(E,Q,T)，其高度仍为 exp(O(n/log n))。
这种 a 的 P_a(t)=sum a_k D_k t^k 非零，但在原正积分密度下积分为零，
所以必在 (0,1/16) 上同时取正值和负值。
因此“任意短消元向量有效”在真实家族中已经被否定。

若 gamma=p/q，则上述全部足够短的余项最终都是绝对值小于 1/q 的 1/q 整数，
因而恰为 0。这与短向量存在相容。

可以改用一个完全有限的双向量证书。给定整数 a、b，核验

```text
E a=E b=0，Delta=u(a)*v(b)−u(b)*v(a)≠0，
H=max(sum|a_k|,sum|b_k|)。
```

则任何 gamma=p/q、q>0 的表示必须满足 qH>2^n。
证明：两向量非零，故 H≥1 且 |r(a)|、|r(b)|<H*2^(-n)。
若 qH≤2^n，两个整数 q r(a)、q r(b) 的绝对值均<1，故均为零，
得到 p u(a)=q v(a)、p u(b)=q v(b)，相乘相减推出 q Delta=0，矛盾。
因此一份核验通过的证书给出严格分母界

```text
q≥floor(2^n/H)+1。
```

还可以保留真实积分上界，令 N=16^(2n)、w_k=D_k*16^(2n-k)，
C_+(x)=sum max(x_k,0)*w_k、C_-(x)=sum max(-x_k,0)*w_k，
并取 C=max(C_+(a),C_-(a),C_+(b),C_-(b))。
对非零 x，正积分界给 -C_-(x)/N<r(x)<C_+(x)/N；
即使某个符号部分为空，另一部分的严格正性仍保证两端严格。
所以同一整数反证得到更强的 qC>N，即 q≥floor(N/C)+1。
这种证书只需 C/16^(2n)→0；其有效双向量族仍未构造出来。

若能在无界多个 n 上构造这种证书，并证明 H/2^n→0，就能直接推出无理性。
核验字段全是从原幂积计算的整数，没有把无理性写成证书字段。
**目前没有证明这样的证书族存在。** 上面的鸽巢论证仅保证一个非零核向量，
不保证两个有效投影；增广秩增加 2 也不提供所需长度界。
普通子式构造仅给系数 s!*H_n^s，s=rank E，其对数 O(n^2/log n) 过大。

另一可检验充分条件是找到同样足够短的 a，使
P_a(t)=sum a_k D_k t^k 在 [0,1/16] 非负且非零。
由原正积分密度可得 r(a)>0，从而在有理性下产生正而趋零的 1/q 整数。
一般混合符号的核向量不具备这种正性；所需向量族也未证明存在。
完整推导及一般矩阵上短向量全部无效的反例见
[质数对数消元报告](../docs/paper_sondow_log_cancellation_20260905_zh.md)。

原幂积还给出精确支撑 E_(p,k)>0 当且仅当 p≤2k：每个底数 k+1,…,2k
的指数都正，且每个 p≤2k 都在这一区间内有倍数。
对 p∈(2n,4n]，首个非零列为 k=(p+1)/2，由此得到正对角上三角子式，
证明 rank E≥pi(4n)−pi(2n)。它未控制 Q、T 的有效方向。
在有限层 n=31，模素数 1009 的非零子式确证 rank E=30、
rank[E;Q;T]=32，说明有效二维方向真实存在；n=34 时二者为 32、34，
而列数为 35，说明有效方向与公共核真实共存。
这些有限证据不证明渐近存在性或短长度界。

尤其，若 E a=0、Q a=0、T a≠0，则 |r(a)|=|T a|≥1，
从而 ||a||1>2^n。直接用逆矩阵选取纯 T 方向无法得到上述非平凡分母界。
真实支撑证明、公共核短向量证明及可复算有限整数证据见
[真实核结构稿](../docs/paper_sondow_kernel_structure_20260905_zh.md)。

在 n=31 层还得到一个严格有限障碍，而不只是搜索失败。
两条明确整数核向量的所有二阶子式 gcd 为 1，结合 rank E=30，证明它们生成
整个二维整数核。按上述 w_k 加权后的 Gram–Schmidt 平方长度 g1、g2，
精确检查分别在二次幂区间 [2^4952,2^4953)、[2^4955,2^4956)。
任何非零整数核向量的加权欧氏平方范数≥min(g1,g2)>2*(16^62)^2；
其正负加权和 C(x) 又满足 norm2(Wx)^2≤2*C(x)^2。
故这一层所有非零整数核向量都满足 C(x)>16^62，强化证书只能给出 q≥1。
这一结论不涉及其他 n，也不排除其他数论证明方法。
完整整数数据、独立标准库核验器及证明见
[n=31 有限层障碍](../docs/paper_sondow_n31_obstruction_20260905_zh.md)。

当公共核 K=ker_Z(E,Q,T) 非零时，可以只考察有效商格。
从完整整数核基出发，用整数可逆换基写成 [C,a,b]，C 生成 K，
a、b 的 (Q,T) 投影构成整个整数像的基。
将加权向量投影到 span_R(WC) 的正交补，商格为二维，Gram 矩阵为精确有理数。
整数 Gauss 换基使其满足 0<alpha≤delta、2|beta|≤alpha；
对非零整数 (x,y)，二次型≥alpha*(x²-|xy|+y²)≥alpha，
所以最短平方恰为 alpha。
若 alpha>2*(16^(2n))²，则每个有效整数向量都满足 C(x)>16^(2n)，
这一层的强化证书同样只能给出平凡界。
这是已证明的单层充分判据，尚未对无穷多个实际矩阵验证；
阈值未通过也不能反推存在低成本向量。完整矩阵证书及证明见
[有效商格障碍](../docs/paper_sondow_quotient_obstruction_20260905_zh.md)。

该判据又在四个真实层独立核验通过：n=34、48、64、96 的有效商格最短平方
分别落在二次幂指数为 574、794、1037、1547 的区间内，
严格超过阈值 2N² 的指数 545、769、1025、1537。
核验使用完整整数核的互素子式证书、整数可逆换基及精确投影线性方程，
不依赖 LLL 质量或浮点近似。
因此这四层所有有效方向都满足 C(x)>N；并非只说某次搜索没有找到好向量。
这些有限事实不决定其他层，更不提供任何渐近结论。
数据和标准库独立复算方法见
[四层有效商格证书](../docs/paper_sondow_finite_quotient_certificates_20260905_zh.md)。

还有一个无需正交投影的实际像指数判据。
令 d_img=[Z²:(Q,T)(ker_Z E)]，B_star=binom(4n,2n)。
由 Q_k/w_k=B_k*16^(k-2n)≤B_star，分别估计正负部分得
|Q·x|≤B_star*C(x)。对有效双向量，d_img 整除其非零投影行列式，且

```text
d_img≤|Delta|=|(Q·b)r(a)-(Q·a)r(b)|<2*B_star*C²/N。
```

所以 C²>d_img*N/(2B_star)；若 d_img≥2*N*B_star，
这一层全部双向量的 C>N，即使等号也排除非平凡证书。
完整整数核基的投影二阶子式 gcd 给出 d_img，不能用任意一对向量的行列式代替。

目前从真实结构直接保证的因子为 2D_n|d_img：每个 Q_k 被 2D_n 整除。
该因子远不足以满足上述阈值。另一方面，真实残差使有效映射的两个行方向
近似线性相关，直接推出的是商格面积下界，不能倒写成两条短方向的存在性。
即便获得面积上界，还须控制第二独立方向及从实投影提升为整数代表的成本。
这些精确体积公式与尚未证明的渐近条件见
[像指数与协体积证明](../docs/paper_sondow_quotient_volume_20260905_zh.md)。

像指数还可准确拆成 d_img=g_Qimg*h_T，其中 g_Qimg 是 Q(ker_Z E) 的正生成元，
h_T 是 T(ker_Z(E,Q)) 的正生成元。选取 Q 像为 g_Qimg 的向量后，
任意像减去它的整数倍就落在纯 T 像，故两者乘积恰为指数。
这比只估计矩阵条目的素数支持更精确：真实 n=31 的指标具有大于 124 的素因子，
全部落在 h_T；后四个已核验层的指标则只含≤4n 的素因子。
这些有限事实没有证明后续层全部满足同一性质。
在只允许小素数分母的环内把 Q_k 归一化，可把指标没有大素因子的条件写成
两个准确的线性方程；目前没有证明它们对充分大 n 总能求解。
分解、局部饱和条件、五层完整因子数据与独立复算见
[像指标的算术结构](../docs/paper_sondow_image_index_arithmetic_20260905_zh.md)。

### 7.5a 原积分的更强有理上界与成本修正

前述有限层障碍针对已经指定的成本 C，不能排除使用更细积分界的证书。
直接对原积分分母可以证明，对全部 k≥1 有

`0<I_k<1/(4k² B_k²)≤16^(-k)/k`。

确实，0<x<1 上 -log x>2(1-x)/(1+x)，对 y 同样估计，相加并乘 1-xy，
再用 (1-xy)²-(1-x²)(1-y²)=(x-y)²≥0，得到

`-(1-xy)log(xy)>4(1-x)(1-y)`。

原被积函数因此严格小于
x^k(1-x)^(k-1)y^k(1-y)^(k-1)/4，后者可积。
两次有限分部积分给单变量积分 k!(k-1)!/(2k)!=1/(k B_k)，得第一个严格界。
归纳 B_k²≥16^k/(4k)，归纳步两边所需差为 (2k+1)²-4k(k+1)=1，得第二个界。

现改用有理权重 v_k=D_k/(4k²B_k²)，将两个核向量的正负加权和的最大值记为 C_beta。
仍保留 Delta≠0。原余项满足 -C_beta,-(a)<r(a)<C_beta,+(a)，
所以有理性 gamma=p/q 强制 q*C_beta>1，给 q≥floor(1/C_beta)+1。
令 theta_k=16^k/(4k²B_k²)，则 theta_1=1，且
theta_(k+1)/theta_k=4k²/(2k+1)²<1。与前节原成本的准确比较为

`theta_(2n)*C/N≤C_beta≤theta_n*C/N≤C/(nN)`，N=16^(2n)。

因而原证书还可加强为 q*C>nN；然而有效双向量族仍没有构造出来。
旧商格最短平方 alpha 只在满足

`alpha>32(2n)^4 binom(4n,2n)^4`

时保证新成本的全部有效方向仍>1。这个阈值来自
||Va||²≥theta_(2n)²*alpha/N² 和 ||Va||²≤2*C_beta(a)²。
独立整数核验在 n=34、48 通过，在 n=64、96 未通过；后两层只能说
这一比较未判定，不能反推有低成本整数代表。
全参数积分证明、严格端点和准确比较见
[加强积分界与新权重](../docs/paper_sondow_beta_integral_bound_20260905_zh.md)。

### 7.5b 保留积分交叉项的证书与新的精确有限障碍

只对各系数取绝对值可能丢掉整个多项式的抵消。令
beta_m=1/(4m²B_m²)、t=x(1-x)y(1-y)、d=-(1-xy)log(xy)，
对 a 的索引 k=n+i 定义 c_i=a_(n+i)D_(n+i)、F_a(t)=sum c_i t^i。
原消元余项为 r(a)=∫∫t^n F_a(t)/d。

测度 t^n/d 的质量为 I_n，Cauchy–Schwarz 给
r(a)²≤I_n∫∫t^n F_a²/d。第 7.5a 节的严格分母界作用于整个非负平方，得到

`|r(a)|²<U_n(a)²=beta_n sum_(i,j) c_i c_j beta_(n+i+j)`，a≠0。

不能对有符号的交叉项分别套同方向的不等式。右端是具有有理系数的正定二次型：
它等于 beta_n 乘 F_a² 在有限正测度 t^n/[4(1-x)(1-y)] 下的积分。
非零多项式在 t∈(0,1/16) 不会处处为零，故正定且严格，包含 r(a)=0 的情形。
对真实整数核中的有效双向量 a、b，令 M=max(U_n(a)²,U_n(b)²)，则

`gamma=p/q ⇒ q²M>1 ⇒ q≥floor(sqrt(1/M))+1`。

因为两个 q r 不可能同时为零，其中一个非零整数的平方≥1，再用严格上界即可。
M=1 仍排除 q=1，所以排除这类证书的成本门槛必须严格大于 1。

新二次型并非对所有向量都优于原 C_beta，但能证明准确常数比较。
令 z_i=c_i beta_(n+i)，其正负和为 P、N_-=sum max(-z_i,0)，并令
kappa_n²=beta_n beta_(3n)/beta_(2n)²。
beta 的相邻比值严格递增，给归一化矩阵条目位于 [1,kappa_n²]。
中央二项式的相邻比值也严格递增，给 kappa_n²<16/9。于是

`U_n(a)²≤kappa_n²(P²+N_-²)-2PN_-≤kappa_n² C_beta(a)²`。

真实非零 E 核的系数必有两种符号，因为 E_(2,k)>0，所以第一处最终上限还可取严格。
安全组合方式是逐向量取 W_n(a)=min(U_n(a)²,C_beta(a)²)，再对双向量取最大；
两个余项界都严格，组合后仍是有效证书。尚未证明无界参数上存在成本趋零的有效族。

新矩阵也可作精确商格认证。使用已认证完整核基及整数可逆换基，
在这个正定内积下沿公共核作正交投影；以整数交叉乘法核验 Schur 投影方程，
再用整数 Gauss 换基得到最短非零平方 alpha。
对全部有效方向 U_n(a)²≥alpha；若 alpha≥16/9，则上述严格比较还给 C_beta(a)>1。

四层原始整数数据现已全部独立核验：n=34、48、64、96 的 alpha 分别位于
二次幂指数 20、16、4、2 的区间内，均严格超过 16/9。
因此这四层的每个有效方向都有 U_n(a)²>1 且 C_beta(a)>1，连逐向量取较小值
的组合证书也不能给出非平凡分母界。这以新的证据补齐了前节旧比较未判定的两层。
检查器从原三重指数和及完整整数核认证出发，不使用候选生成器的 LLL 或浮点质量。
这些仍然只是四个有限层定理，不能外推到所有 n。

一般积分证明、比较与第二连续极小值判据见
[有理二次型证书](../docs/paper_sondow_moment_quadratic_certificate_20260905_zh.md)，
完整新数据、缩放因子及标准库核验命令见
[四层积分二次型障碍](../docs/paper_sondow_moment_finite_obstructions_20260905_zh.md)。

### 7.6 当前归约义务

仍需从本证书的特殊数论内容，独立构造到 G_n 的实际 PA 证明转换，
或直接给出在有理性下正确的 G_n 证明生成器，并证明其完整载荷界。
截至本稿，尚未找到这样的构造。
合取、析取及抽象长度投影的其他障碍见
[对象转换引理](../docs/paper_route_global_gate_20260905_zh.md)。
本节定位了有限可靠性方案的反射成本，不是对所有潜在 Sondow 归约的否定定理。

## 8. 与当前代码的关系及继续顺序

旧 `full_sondow_certificate_accepted` 在 `EulerLimit/Certificate.lean` 中的首项
就是有理参数等于 gamma 的实数命题；其 `checked` 用法是命题性的。
`mainSondowFullCertificateCheckedCodeSemantics` 的代码类型为有理数提升类型，
并把 size 定义为 1；它没有实现本稿的有理区间运算轨迹。
故本稿第 3 节是纸面上的替代构造，不是对旧代码已具备功能的描述。

继续顺序：先完成第 7 节的实际归约，同时补齐第 6 节同一直接谓词的具体数学条件；
整条纸面证明核查通过后，才将这些构造形式化。
本稿的局部引理不得把 M17、M20 或最终无理性结论标为已证。
