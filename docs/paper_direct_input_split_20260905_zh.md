# 公开载荷与两个内部列表：同一 InputSplit 的纸面证明

日期：2026-09-05。仅纸面推导，不新增 Lean。

本引理证明当前公开 raw token 流，经实际 InputSplit 和初态比较，恰是内部 proof
与 certificate 两个列表的拼接；规定燃料中的 inputTokenCount 因而是它们的长度和。
同时构造位数关于公开完整载荷多项式有界的规范输入表。
它不处理后续 parse/combine 单步关系，也不宣布条件 (1)–(3) 完成。

## 1. 使用的实际关系

以下文件均位于 integration：

- `FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit.lean:37`：
  `split≤M`，raw `[0,split)` 与 source `[proofStart+1,proofFinish)` 相等，
  raw `[split,M)` 与 source `[certificateStart+1,certificateFinish)` 相等。
- `FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula.lean:44`：
  source 两个含长度头的 slice 分别等于初态的 `[e3,e5)`、`[e5,e7)`。
- `FoundationCompactNumericListedDirectVerifierStateFormula.lean:76`：
  初态前两个子式分别是 `NatListSlice(e0,e1,e2,e3,e6,e5)` 和
  `NatListSlice(e0,e1,e2,e5,e8,e7)`。
- `FoundationCompactNumericListedDirectAdditiveCodecGraph.lean:97`：
  `NatListSlice` 的 bodyStart=start+1、finish=bodyStart+count，长度头的行值为 count。
- `FoundationCompactNumericListedDirectCrossTableSliceEquality.lean:25`：
  比较相同长度的两个 slice，在两宽度之和内逐位比较，并在较小宽度以上补零。

记 raw 表为 A、宽度 W、行数 M，初态表为 H、宽度 V。行值使用已在主稿 5.3 节
证明正确的 `Row(T,w,i)=(T div 2^(iw)) mod 2^w`。表格以上的额外高位不影响指定行。

## 2. 跨表 slice 关系的 PA 行值刻画

对两张表及两个 slice，实际 CrossEq 关系在 PA 内等价于：存在共同长度 c，满足
原有各端点和行数界，而且对每个 i<c，两个对应 Row 值相等。

证明：任取对应两行 u、v。它们分别小于 2^w、2^w'。在每个 j<w+w' 上，
原 CrossEq 恰要求这两个行值的第 j 位相等：j 超过某一行宽时，该行值小于 2^j，
所以其位为零；j 在行宽内时，用主稿 5.3 的行提取等式。
将 u、v 都看作宽度 w+w' 的数，有限位外延性给 u=v。
反之，若 u=v，则其两种宽度范围内的位相同，超过较小宽度的位同为零，
得到原来的全部受限位等价。两宽度均为零时 u=v=0，位量词为空，同样成立。

证明只使用商余唯一性、有限位外延性及固定次数量词推导，因此可在 PA 内进行。
特别地，可以把两层 CrossEq 串成实际行值的相等，而不要求两个表格数或行宽相同。

## 3. 长度头带来的精确计数

从初态 StateCore 的两个 NatListSlice 消去 bodyStart，有

```text
e5=e3+1+e6，e7=e5+1+e8。
```

source proof slice 到初态 proof slice 的 CrossEq 具有共同长度，因而

```text
proofFinish=proofStart+1+e6。
```

InputSplit 的 raw proof 比较又直接给

```text
proofFinish=proofStart+1+split。
```

自然数加法消去得 e6=split。证书一侧同理：
raw `[split,M)` 的长度 c 满足 M=split+c，且
`certificateFinish=certificateStart+1+c`；初态比较给相同式子中的 c=e8。
所以

```text
split=e6，M=split+e8=e6+e8。                         (3.1)
```

这里只使用原端点等式，不先假设两个列表的 Lean 解码存在，也没有从 Nat 减法
截断中丢失条件。split≤M 已是原 InputSplit 的首项。

## 4. 所有 token 逐项相同

定义初态 proof 的第 i 项为 `p_i=Row(H,V,e3+1+i)`，0≤i<e6；
certificate 的第 j 项为 `c_j=Row(H,V,e5+1+j)`，0≤j<e8。
这些是按有限行号定义的数列，不需要额外语法正确性。

对 i<split，InputSplit 的前半 CrossEq 得

```text
Row(A,W,i)=Row(source,sourceWidth,proofStart+1+i)。
```

初态 proof CrossEq 在 offset=1+i 处给右端等于 p_i。
这个 offset 合法，因为完整 slice 的长度是 1+e6=1+split。

对 split≤i<M，取 j=i-split；由 (3.1) 有 j<e8 及 split+j=i。
同样在证书两层 CrossEq 中分别取 offset=j、offset=1+j，得到
`Row(A,W,i)=c_j`。

因此 PA 可证明 raw 数列逐项等于 `[p_0,...,p_(e6-1)]` 与
`[c_0,...,c_(e8-1)]` 的拼接，且长度恰为 e6+e8=M。
有限数列的存在可直接用主稿 5.3 的固定宽度逐行追加归纳构造。

结合规范 packed token 表的双向编码引理，公开码确是上述 raw 拼接的 packed 码，
原 inputWidth W 恰是其 payload 位数。因此 PA 中的规定燃料可以合法改写为

```text
4*(inputTokenCount+1)+8 = 4*(e6+e8+1)+8。           (4.1)
```

这去掉主稿 5.4 燃料引理此前保留的输入长度校准义务。
它不证明两个列表一定组成语法正确的证明树及证书；这一点属于规则运行层。

## 5. 反向规范输入表及完整位数界

现给定两个自然数 token 数列 P、C，长度分别为 p、c，令 M=p+c，
令 W 为 raw 拼接 P++C 的实际 binaryNat payload 位数。
每个 token t 恰占 2*ell(t)+2 位，故

```text
W=2*sum_(t in P++C)(ell(t)+1)，2M≤W。
```

其中 ell(0)=0。source 流使用实际 additive Nat-list 编码，恰为

```text
sourceTokens=[p]++P++[c]++C，sourceTokenCount=M+2。
```

其规范宽度 H 为这个流的 binaryNat payload 位数，因此

```text
H=W+2ell(p)+2ell(c)+4
 ≤W+4ell(M)+4
 ≤W+4M+4≤3W+4。                                  (5.1)
```

取 raw 固定宽度表 A、raw offset 表 O 以及 source 固定宽度表 B，
各自按主稿 5.3 的逐行追加构造，选取

```text
split=p，proofStart=0，proofFinish=p+1，
certificateStart=p+1，certificateFinish=M+2。
```

前半 raw 第 i 行与 source 第 1+i 行相同；后半 raw 第 p+j 行与 source
第 p+2+j 行相同。第 2 节的行值刻画给原 CrossEq，所有端点等式和行数界逐项成立。
raw 的 CanonicalAtWidth 由主稿 5.3 保证。所以这是同一 InputSplit 的实际逆向见证，
不是另换一个语义上相似的接口。

用宽度 w 存放 r 行的规范表小于 2^(rw)。所有 raw token 适合宽度 W，
offset≤W<2^W；source token 适合宽度 H。因此

```text
ell(A)≤M*W，ell(O)≤(M+1)*W，
ell(B)≤(M+2)*H≤(M+2)*(3W+4)。                     (5.2)
```

以上均为 W 的固定二次界；端点和各计数的位数更小。
空流边界 p=c=M=W=0 时 H=4，sourceTokens=[0,0]，A=O=B=0，
所列两个 slice 都是空 body，长度头各为 0，全部条件成立。

这些小表是新构造出的规范见证。不能反推输入中任意满足公式的表本身都如此小：
原公式允许指定行之外存在高位，也允许更宽的内部表。
本引理只规范化输入流与 source slice；把原接受运行一并换到新表上，仍需独立的
运行矩阵输运证明。

## 6. 可供整体证明使用的结论

- 同一 InputSplit 与初态 StateCore/Initial 条款在 PA 内推出 raw=proof++certificate；
  inputTokenCount 是两个真实内部列表的长度和。
- 对实际给定 raw 载荷，规范 raw/source/offset 表可以构造，位数关于 W 二次有界。
- 规定燃料的 token 参数校准已补齐。
- 后续规则验收、内部解析轨迹与429列矩阵的完整存在性未由本引理完成。
