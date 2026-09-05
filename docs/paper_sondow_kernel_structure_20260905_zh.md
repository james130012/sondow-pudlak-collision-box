# 真实 Sondow 核的结构：三角素数行、短零余项与有限秩证据

日期：2026-09-05。本文只研究真实 Sondow 指数矩阵，承接
[质数对数消元报告](paper_sondow_log_cancellation_20260905_zh.md)。

已得到三个结论：原幂积给出明确的三角素数行；真实公共核中无条件存在
exp(O(n/log n)) 的非零短向量，其组合余项恰为零；有限整数计算显示有效的二维
投影确实会出现，但这没有提供所需的短双向量证书族。

## 1. 固定真实对象

令 k=n,…,2n，D_k=lcm(1,…,2k)，Q_k=D_k binom(2k,k)，
T_k=D_k sum(i=0,…,k) binom(k,i)^2 H_(k+i)。
对 p≤4n 的质数，E_(p,k)=v_p(S_k)。所有这些都是实际 Sondow 对象。

把原幂积的同底数指数合并，得到

```text
S_k=product(j=1,…,k) (k+j)^e_(k,j)，
e_(k,j)=2 sum(i=0,…,min(j−1,k−j))
             binom(k,i)^2 * sum(h=i+1,…,k−i) (D_k/h)。
```

每个 D_k/h 都是整数。原恒等式给出，对于 E a=0 的整数向量 a，

```text
u(a)=sum a_k Q_k，v(a)=sum a_k T_k，
r(a)=sum a_k D_k I_k=gamma*u(a)−v(a)，
|r(a)|<2^(−n)||a||_1  （a≠0）。                     (1)
```

本文使用已核查的原恒等式与 I_k 的积分表示，来源：
[Sondow 原文](https://arxiv.org/pdf/math/0209070)。

## 2. 精确质数支撑与三角子式

**引理 1。** 对所有 k≥1 和质数 p，

```text
E_(p,k)>0 当且仅当 p≤2k。                           (2)
```

证明：每个 e_(k,j)>0，因为 i=0 的求和项已经严格为正。
若 p>2k，原幂积没有能被 p 整除的底数。
若 k<p≤2k，底数 p 自身出现。若 p≤k，取严格大于 k 的最小 p 倍数，
它不超过 k+p≤2k，也作为底数出现。因此指数为正。证毕。

于是 p≤2n 的各行在整个 [n,2n] 区间都严格为正。
对 p in (2n,4n]，p 为奇素数，记 k_p=(p+1)/2。式 (2) 给出

```text
E_(p,k)=0，当 k<k_p；
E_(p,k)>0，当 k≥k_p。
```

把这些 p 从小到大排列，并选择对应列 k_p，得到一个对角元为正的上三角子矩阵。
不同奇素数对应不同 k_p，所以

```text
rank(E)≥pi(4n)−pi(2n)。                             (3)
```

这些是明确可用的枢轴行，却不是每行只在一个地方出现。
只有当 4n−1 为素数时，相应行在整个区间内仅有最后一列非零，
从而任何 E 核向量都满足 a_(2n)=0。
更一般地，若 j 是某非零 E 核向量最大的非零坐标索引，那么 2j−1 必不是素数：
否则 p=2j−1 行的所有较小列为零，较大列的系数也为零，便强制 a_j=0。

式 (3) 没有包含 Q、T 两行，不能据此推出增广秩增加 2，
也不能据此推出有效投影方向具有很小的整数系数。

## 3. 实际公共核中存在同样量级的短零余项

令 m=n+1、r=pi(4n)，并定义真实增广矩阵

```text
M=[E;Q;T]，K_n=ker_Z M。
```

此前报告使用的整数高度

```text
H_n=8n(2n+1)^3*36^(2n)
```

同时支配 M 的所有条目。E 的界已证；而 D_k<8^k、binom(2k,k)≤4^k，故

```text
Q_k<32^k≤32^(2n)。
```

由 sum(i=0,…,k) binom(k,i)^2=binom(2k,k) 以及 H_(k+i)≤2k，

```text
0<T_k≤2k Q_k≤4n*32^(2n)≤H_n。
```

这里二项式等式可取 (1+x)^k*(1+x)^k 中 x^k 的系数得到。
因此 log H_n=O(n) 对完整增广矩阵仍成立。

充分大的 n 上 r+2<m。把前一报告的鸽巢证明直接用于 M，得到非零整数 a，满足

```text
E a=0，Q a=0，T a=0，
||a||_infinity≤floor((mH_n+1)^((r+2)/(m−r−2)))+1
              =exp(O(n/log n))。                    (4)
```

由于实际 r=O(n/log n)，增加两个约束没有改变该量级。
式 (1) 随即无条件给出 r(a)=0；这不依赖 gamma 有理或无理。

因此，对于真实 Sondow 家族，确实存在与第一 Siegel 短向量同阶的非零消元向量，
其余项恰为零。这直接排除了“任何这种短消元向量都会产生非零余项”的加强命题。
式 (4) 没有声称某个指定算法返回的最短向量一定在 K_n，
也没有排除在同一长度级别还存在其他有用向量。

### 3.1 这些向量对应的真实积分多项式必定变号

对任意非零 a in K_n，定义

```text
P_a(t)=sum(k=n,…,2n) a_k D_k t^k。
```

它不是零多项式，因为各幂次不同且 D_k>0。
Sondow 的真实积分表示给出

```text
integral over (0,1)^2 of
 P_a(x(1−x)y(1−y))/[−(1−xy)log(xy)] = r(a)=0。
```

积分权在开正方形上严格为正，t=x(1−x)y(1−y) 的取值包含整个 (0,1/16)。
若 P_a 在该区间始终非负或始终非正，非零多项式在某个开区间的严格同号性
将使积分严格同号，与零相矛盾。所以 P_a 必在 (0,1/16) 内同时取正值和负值。

式 (4) 因而还给出一族真实、系数受控、积分恰好抵消的变号多项式。
原来每个 I_k>0 的事实，不能将这些组合改判为严格正余项。

## 4. 三个有限层的精确整数证据

对 n=24、31、34，从原幂积精确构造矩阵后，在素域 F_1009 上消元。
1009 的素性可对 2,…,31 试除直接验证。
所列模秩达到了相应行数或列数上限，因此给出有理数域上的精确秩，而非仅数值猜测。

| n | 列数 | rank(E) | rank([E;Q]) | rank([E;Q;T]) | dim K_n |
| --- | ---: | ---: | ---: | ---: | ---: |
| 24 | 25 | 24 | 25 | 25 | 0 |
| 31 | 32 | 30 | 31 | 32 | 0 |
| 34 | 35 | 32 | 33 | 34 | 1 |

其中各行 E 按质数递增排列，列按 k 递增排列。以下非零子式值均取模 1009：

| n | 矩阵及选择的列 | 行列式余数 |
| --- | --- | ---: |
| 24 | E，k=24,…,47 | 574 |
| 24 | [E;Q]，k=24,…,48 | 726 |
| 31 | E，k=31,…,60 | 511 |
| 31 | [E;Q]，k=31,…,61 | 685 |
| 31 | [E;Q;T]，k=31,…,62 | 453 |
| 34 | E，k=34,…,64 及 k=66 | 576 |
| 34 | [E;Q]，k=34,…,66 | 15 |
| 34 | [E;Q;T]，k=34,…,67 | 883 |

n=24 的 E 核是一维，因此不可能提供二维投影。
n=31 的有效二维投影确实存在，不能把“所有真实 E 核向量都在公共核”当成规律。
n=34 同时具有有效二维投影和一维非零公共核，两种方向真实共存。
这些有限事实不证明任何渐近秩公式或短双向量界。

### 4.1 n=34 的完全指定零余项反例

取 n=34 的实际 M=[E;Q;T]，它为 34×35 矩阵。对 j=0,…,34，定义整数

```text
a_(34+j)=(-1)^j det(M 删除第 j 列)。                 (5)
```

余子式恒等式给出 M a=0。第 j=34 分量的余数为 883 mod1009，故 a≠0。
这是一条完全由真实 Sondow 整数确定的明确向量定义；并且

```text
E a=0，Q a=0，T a=0，sum(k=34,…,68) a_k D_k I_k=0。
```

它不依赖对 gamma 的未证断言。这里没有声称该余子式向量本身最短；
渐近短零余项的结论来自第 3 节独立证明。

## 5. 纯 T 方向存在一个实际长度障碍

若实际 E a=0、Q a=0，而 T a 是非零整数，则式 (1) 给出

```text
|T a|=|r(a)|<2^(−n)||a||_1，
故 ||a||_1>2^n*|T a|≥2^n。                          (6)
```

这是实际 Sondow 核中的无条件下界。
例如 n=31 的增广方阵 M 可逆，取伴随矩阵乘以对应 T 行的单位列向量，
便得到 E a=0、Q a=0、T a=det(M)≠0 的整数向量。
式 (6) 保证这一纯 T 方向的系数和已经超过 2^n。

所以用增广矩阵逆或伴随矩阵直接选取坐标方向，虽然可以证明二维投影存在，
却不能用这组方向取得非平凡的分母下界。
该结论不排除通过不同方向组合得到更小的双向量；其构造和界仍是待证问题。

## 6. 有限子式的自足复算代码

以下 Python 代码只使用标准库，直接输出第 4 节列出的模行列式。
本次还另外按原三重求和顺序重算了 k=1,…,68 的全部质数指数，
与聚合公式逐项完全相同；没有使用浮点数或对 gamma 的近似值。

```python
from math import comb, isqrt, lcm

def primes_upto(b):
    return [p for p in range(2, b + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]

def source_column(k):
    D = 1
    for h in range(1, 2 * k + 1):
        D = lcm(D, h)
    harmonic = [0]
    for h in range(1, 2 * k + 1):
        harmonic.append(harmonic[-1] + D // h)
    exponents = {}
    for j in range(1, k + 1):
        e = 2 * sum(comb(k, i) ** 2 *
                    (harmonic[k - i] - harmonic[i])
                    for i in range(min(j - 1, k - j) + 1))
        b = k + j
        for p in range(2, isqrt(b) + 1):
            while b % p == 0:
                exponents[p] = exponents.get(p, 0) + e
                b //= p
        if b > 1:
            exponents[b] = exponents.get(b, 0) + e
    Q = D * comb(2 * k, k)
    T = sum(comb(k, i) ** 2 * harmonic[k + i]
            for i in range(k + 1))
    return exponents, Q, T

def block(n):
    cols = [source_column(k) for k in range(n, 2 * n + 1)]
    E = [[c[0].get(p, 0) for c in cols]
         for p in primes_upto(4 * n)]
    return E, [c[1] for c in cols], [c[2] for c in cols]

def determinant_mod(a, p=1009):
    a = [[v % p for v in row] for row in a]
    d = len(a)
    assert all(len(row) == d for row in a)
    ans = 1
    for j in range(d):
        t = next((i for i in range(j, d) if a[i][j]), None)
        if t is None:
            return 0
        if t != j:
            a[t], a[j] = a[j], a[t]
            ans = -ans
        z = a[j][j]
        ans = ans * z % p
        inv = pow(z, -1, p)
        for i in range(j + 1, d):
            c = a[i][j] * inv % p
            for h in range(j, d):
                a[i][h] = (a[i][h] - c * a[j][h]) % p
    return ans % p

assert 1009 in primes_upto(1009)
specs = [
    (24, 0, list(range(24)), 574),
    (24, 1, list(range(25)), 726),
    (31, 0, list(range(30)), 511),
    (31, 1, list(range(31)), 685),
    (31, 2, list(range(32)), 453),
    (34, 0, list(range(31)) + [32], 576),
    (34, 1, list(range(33)), 15),
    (34, 2, list(range(34)), 883),
]
for n, extra, columns, expected in specs:
    E, Q, T = block(n)
    M = E + [Q, T][:extra]
    actual = determinant_mod([[row[j] for j in columns] for row in M])
    assert actual == expected
    print(n, extra, actual)
```

## 7. 对下一步的约束

可以使用第 2 节的三角枢轴减少消元规模，也可以利用第 4 节的有限子式确认
某一层是否具备二维有效投影。但第 3 节证明：真实公共核已有大量可被短向量搜索命中的
退化方向，单纯最小化非零 E 核向量的长度不够。

需要直接构造两条投影行列式非零、且最大系数和 H=o(2^n) 的真实整数向量，
或得到前一报告中的正积分多项式证书并同时控制长度。
这两个条件在本报告中仍未证明，不能由有限秩证据或每个积分的正性代替。
