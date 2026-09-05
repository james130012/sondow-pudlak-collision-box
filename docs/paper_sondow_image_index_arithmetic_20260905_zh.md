# 真实 Sondow 像指标的素数支持与局部缺口

日期：2026-09-05。本文使用已经构造的完整整数核，不生成新核，不进行渐近数值外推。
所研究的是实际 E、Q、T，而不是仅满足高度界的一般矩阵。

已核实 n=34、48、64、96 的像指标全部 4n-smooth；n=31 则确实含有大于 124
的素因子。后一事实不需要分解其巨大余因子。本次得到一个进一步定位：五层的
Q 像公共因子都 4n-smooth，n=31 的全部大素因子出现在纯 T 像的整除条件中。
本文给出普遍成立的分解公式和两个明确的局部模块方程；没有证明这些方程最终总有解。

## 1. 定义与逐次增广公式

固定 k=n,…,2n，使用

```text
D_k=lcm(1,…,2k)，B_k=binom(2k,k)，Q_k=D_k B_k，
T_k=D_k sum(i=0,…,k) binom(k,i)^2 H_(k+i)，
E_(p,k)=v_p(S_k)，p≤4n，
Lambda=ker_Z E，Phi(x)=(Q x,T x)。
```

假设 Phi(Lambda) 秩为 2，令 d_img=[Z²:Phi(Lambda)]。定义三个正整数

```text
g_Qimg=gcd{Q x:x in Lambda}，
g_Timg=gcd{T x:x in Lambda}，
h_T=gcd{T x:x in Lambda，Q x=0}。
```

秩 2 保证三个像均非零。直接投影到 Q 坐标给出

```text
d_img=g_Qimg*h_T，
g_Timg divides h_T，
c_img=d_img/(g_Qimg*g_Timg)=h_T/g_Timg is a positive integer。 (1)
```

证明：选 x_0 in Lambda 使 Q x_0=g_Qimg，再选 x_1 in Lambda 使
Q x_1=0、T x_1=h_T。任意像向量先减去 x_0 像的整数倍，即落入 Q=0 的像；
后者恰由 (0,h_T) 生成。因此这两个像构成整个像格的基，行列式绝对值为
g_Qimg*h_T。T 坐标的总像包含 Q=0 的 T 像，所以 g_Timg 整除 h_T。

若 c_img=1，则像格恰为 g_Qimg Z × g_Timg Z：左侧包含于这个矩形格，且两者
在 Z² 中的指数相同。这里没有把两个像坐标分别可取得误认为可以同时独立取得。

从 E 选满行秩整数行子矩阵 E_0，记 Delta(A) 为满行秩整数矩阵 A 的全部最大阶
子式的正 gcd。由相同的像格投影证明，有

```text
g_Qimg=Delta([E_0;Q])/Delta(E_0)，
h_T=Delta([E_0;Q;T])/Delta([E_0;Q])。                 (2)
```

因此所谓额外大素因子，可以精确区分为第一次增广与第二次增广产生的赋值差。
不能以矩阵条目只含小分母，代替对子式 gcd 的证明。

## 2. 普遍成立的局部判据

设 ell 为任意素数，B 是 Lambda 的完整整数列基，Y=[Q;T]B。则

```text
ell does not divide d_img  iff  rank(Y mod ell)=2。    (3)
```

这是因为 d_img 是 Y 全部 2×2 子式的 gcd。式 (3) 不要求原 E 在模 ell 下保持
有理秩；完整整数核基已经保留了正确的局部核。

设 s=rank_Q E。另一种写法使用 Z_(ell)，即分母不被 ell 整除的有理数环。令

```text
U_ell=rowspan_Q(E) intersect Z_(ell)^(n+1)。
```

这是饱和的秩 s 行模。取其任意局部整数基矩阵 U，则式 (3) 等价于

```text
rank([U;Q;T] mod ell)=s+2。                          (4)
```

证明：U 是自由模中的饱和子模，可以扩充为局部整数可逆方阵的前 s 行；在此基下，
U 的核是后 n+1−s 个坐标张成的自由模，[Q;T] 在这些坐标上的矩阵正是其在
Lambda tensor Z_(ell) 上的像矩阵。式 (4) 因而就是式 (3)。

如果 ell 不整除 Delta(E_0)，可直接用 E_0 替换 U。否则，直接看原 E mod ell
的核可能引入不能从整数核约化得到的向量。正确的一般公式仍是

```text
v_ell(d_img)=min v_ell([E_0;Q;T] 的最大阶子式)
             −min v_ell(E_0 的最大阶子式)。           (5)
```

因此，只验证增广后的模秩比原模秩增加 2，并不能在没有饱和说明时直接替代式 (3)。

## 3. 实际 Q 的小素数支持允许一次明确归一化

令 P_n 为所有不超过 4n 的素数之积，R_n=Z[1/P_n]。每个 Q_k 都是 R_n 中的单位：
D_k 的素因子不超过 2k，而 B_k=(2k)!/(k!)² 的素因子也不超过 2k≤4n。

这是实际 Sondow 结构所给出的归一化，定义

```text
G_k=E 的第 k 列 / Q_k，F_k=T_k/Q_k=A_k/B_k，
G_k in R_n^r，F_k in R_n，r 为所保留的 E 行数。
```

这里既可保留 E 的全部行，也可选 E_0；下述模块方程对两种选择都成立。
取基准索引 k_0=n，对 j=n+1,…,2n 设置

```text
C 的第 j 列=G_j−G_n，h_j=F_j−F_n。                  (6)
```

**命题。** d_img 的全部素因子都不超过 4n，当且仅当下面两个方程在 R_n 中可解：

```text
C z_0=−G_n；                                      (7a)
C z_1=0，h z_1=1。                                (7b)
```

证明：作可逆变量代换 y_k=Q_k x_k，令 u=sum y_k、z_j=y_j（j>n），则
y_n=u−sum z_j。原方程与两个像坐标精确变为

```text
E x=G_n u+C z，Q x=u，T x=F_n u+h z。               (8)
```

式 (7a) 当且仅当存在核向量，其 Q 像为 1；式 (7b) 当且仅当存在核向量，其像为
(0,1)。两者合起来生成整个 R_n²：先用前者得到任意 Q 坐标，再用后者修正 T 坐标。
反过来，像为 R_n² 时这两个向量必然存在。完整像格在 R_n 中成为 R_n²，恰好等价于
其有限指数 d_img 在 R_n 中可逆，即全部素因子不超过 4n。证毕。

特别地，式 (7a) 等价于 g_Qimg 是 4n-smooth，式 (7b) 等价于 h_T 是 4n-smooth。
这也可从式 (1) 得到。所有条目虽然都在 R_n 中，线性方程的解仍可能需要除以
大于 4n 的素数；“系数分母光滑”没有证明式 (7) 的可解性。

要证明“充分大 n 没有大素因子”，可以提供一个对这些 n 有效的真实恒等式族，
明确给出式 (7a)、(7b) 的 R_n 解。等价的整数证书是：对某个 t，构造 a、b in Lambda，
使 Phi(a)=(P_n^t,0)、Phi(b)=(0,P_n^t)。只在有理数域中求解，不能控制解的分母支持。
当前没有得到这种恒等式，也没有证明相关秩最终总为 2。

## 4. 三角素数行没有提供局部单位子式

真实支撑公式 E_(p,k)>0 当且仅当 p≤2k，确实给出有理数域上的三角子式，详见
[核结构报告](paper_sondow_kernel_structure_20260905_zh.md)。但其正对角元未必为 R_n 单位。

一个完全实际的小例子是 n=2，取 p=5、7 两行与 k=3、4 两列。原幂积公式直接给出

```text
[[760, 3500],
 [  0,25900]]，
760=2^3*5*19，25900=2^2*5^2*7*37。                 (9)
```

该三角子式含有 19、37 两个大于 4n=8 的素因子。计算时使用
E_(5,3)/D_3=2[H_3+9(H_2−H_1)]=38/3，以及
E_(7,4)/D_4=2[H_4+16(H_3−H_1)]=185/6。
这不声称这些素数整除该层的 d_img；它只直接否定“正三角对角元只含小素因子”
这一可能的补桥理由。模秩或子式 gcd 还需要额外恒等式。

## 5. 已有五层数据的独立精确核验

本次对每层读取已有的完整整数核 basis，按 D_k、B_k、H_(k+i) 的定义独立重算 Q、T，
再重算 Y 的全部 2×2 子式 gcd。结果全部等于提供的 index；没有重新生成或搜索整数核。
完整性的数学依据及可核验变换条件见
[逐条同余构造说明](paper_sondow_integer_kernel_congruence_20260905_zh.md)。
下节复核程序改用已经归档并独立认证的完整核；其像指标、坐标 gcd 与本节结果相同。

对因子文件还逐项核验：所列 p 为素数、p≤4n、指数为正；乘积乘余因子恰等于指标；
余因子不能被任何 p≤4n 整除。位长 b 表示 2^(b−1)≤整数<2^b。

| n | d_img 位长 | 剩余因子 | 已列最大素数 | g_Qimg 位长 | g_Timg | h_T | c_img |
| --- | ---: | --- | ---: | ---: | ---: | --- | --- |
| 31 | 4638 | C_31，位长 4316 | 113 | 313 | 3 | 564 C_31 | 188 C_31 |
| 34 | 339 | 1 | 127 | 329 | 6 | 1320 | 220 |
| 48 | 482 | 1 | 173 | 474 | 2 | 312 | 156 |
| 64 | 658 | 1 | 211 | 656 | 4 | 4 | 1 |
| 96 | 1004 | 1 | 317 | 1003 | 2 | 2 | 1 |

五个 g_Qimg 均只含 p≤4n 的素因子。因此 n=31 的全部大素因子都来自 h_T，
即准确落在式 (7b) 的障碍中。n=64、96 的像格恰为第 1 节所述矩形格。

C_31>1 且没有 p≤124 的素因子，因此必有大于 124 的素因子；无须假设 C_31 本身为素数。
其十进制文本（无换行）的 SHA-256 为
`4c65cc74ed80f3598963bd09d6dc82f9e02255d36607fbda2785dd9d3b850a38`。
这给出实际层反例，排除“对每个秩 2 层，d_img 总是 4n-smooth”。它没有排除
“从某层开始总是光滑”的命题；四个后续成功层也没有证明后一命题。

## 6. 因子记录及简短复核程序

五份完整因子文件已归档为
`paper/computations/sondow_image_index_factors_n{n}_20260905.json`，包括 C_31 的全部十进制数字。
核基直接复用项目内已认证证书：n=31 使用 `sondow_n31_kernel_obstruction_20260905.json`
的 a、b；其余四层使用 `sondow_quotient_obstruction_n{n}_20260905.json` 的 basis。
这些文件均位于 `paper/computations/`；无需复制巨大整数核或读取临时文件。

以下分组记录中“e: p 列表”表示
这些 p 的指数均为 e。除 n=31 还乘 C_31 外，其余四行都是完整素因子分解。

```text
n=31:
  9: 2
  7: 3
  6: 13
  5: 5
  4: 17, 19, 23, 29, 31
  3: 7, 47
  2: 11, 37, 41, 43, 53, 59, 61
  1: 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113

n=34:
  11: 2
  6: 3, 13, 17
  4: 5, 19, 23, 29, 31
  3: 7, 11
  2: 37, 41, 43, 47, 53, 59, 61, 67
  1: 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127

n=48:
  11: 2
  6: 3, 17, 19, 23
  4: 7, 29, 31, 37, 41, 43, 47
  3: 5, 13
  2: 11, 53, 59, 61, 67, 71, 73, 79, 83, 89
  1: 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173

n=64:
  11: 2
  8: 17, 19
  6: 23, 29, 31
  5: 3, 7
  4: 5, 37, 41, 43, 47, 53, 59, 61
  3: 11
  2: 13, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127
  1: 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211

n=96:
  11: 2
  10: 23
  8: 29, 31
  6: 3, 37, 41, 43, 47
  4: 5, 53, 59, 61, 67, 71, 73, 79, 83, 89
  3: 7, 11, 13
  2: 17, 19, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191
  1: 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317
```

下面的程序从项目根目录运行，只读取项目内已有证书，并按原定义做整数算术。
它核验指标与因子记录；完整核的独立认证分别由
`check_sondow_n31_obstruction.py`、`check_sondow_quotient_obstructions.py` 承担，
两者都位于 `paper/computations/`。不能用“基向量落在核内”代替完整性。

```python
import json, math, sys
from pathlib import Path
from functools import lru_cache
sys.set_int_max_str_digits(0)
root = Path('paper/computations')

def prime(p):
    return p >= 2 and all(p % t for t in range(2, math.isqrt(p) + 1))

@lru_cache(None)
def QT(k):
    D = math.lcm(*range(1, 2*k + 1))
    hs = [0]
    for j in range(1, 2*k + 1):
        hs.append(hs[-1] + D // j)
    Q = D * math.comb(2*k, k)
    T = sum(math.comb(k, i)**2 * hs[k+i] for i in range(k+1))
    return Q, T

for n in (31, 34, 48, 64, 96):
    fac = json.loads((root / f'sondow_image_index_factors_n{n}_20260905.json').read_text())
    name = ('sondow_n31_kernel_obstruction_20260905.json' if n == 31 else
            f'sondow_quotient_obstruction_n{n}_20260905.json')
    cert = json.loads((root / name).read_text())
    basis = [cert['a'], cert['b']] if n == 31 else cert['basis']
    src = [QT(k) for k in range(n, 2*n+1)]
    Y = [tuple(sum(a[k]*src[k][j] for k in range(n+1))
               for j in (0, 1)) for a in basis]
    d = math.gcd(*(u*s-v*r for i, (u, v) in enumerate(Y)
                   for r, s in Y[i+1:]))
    factors, cofactor = fac['small_prime_factors'], int(fac['unfactored_cofactor'])
    assert d == int(fac['index']) > 0
    assert all(prime(p) and p <= 4*n and e > 0 for p, e in factors)
    assert math.prod(p**e for p, e in factors) * cofactor == d
    assert all(cofactor % p for p in range(2, 4*n+1) if prime(p))
    gQ, gT = (math.gcd(*(y[j] for y in Y)) for j in (0, 1))
    assert d % (gQ*gT) == 0
    leftovers = []
    for value in (gQ, gT, d // (gQ*gT)):
        for p, _ in factors:
            while value % p == 0:
                value //= p
        leftovers.append(value)
    assert leftovers == [1, 1, cofactor]
    print(n, 'd_bits:', d.bit_length(), 'gQ_bits:', gQ.bit_length(),
          'gT:', gT, 'h_T_bits:', (d // gQ).bit_length(),
          'coupling_bits:', (d // (gQ*gT)).bit_length())
```

即使最终证明 d_img 只含小素因子，还需控制其赋值和有效商格的第二短方向，
才能服务于低成本双向量证书。素数支持本身既不给出 d_img 的所需数量界，
也不提供两个小系数代表。本文没有把这个局部问题误写成无理性证明的完成。
