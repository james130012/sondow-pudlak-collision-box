# 同一内部 MP 定理的短实例化：条件成本定理

日期：2026-09-05。仅纸面证明，不新增 Lean，不把固定内部 MP 定理的依赖省略。

本文具体定义一个可短核验的 SynImp，构造其真实公式码实例的短 PA 证明，再用
当前 cut/exs/closed 树对固定内部定理作四次全称实例化。所得成本按完整树与
结构证书的 binaryNat payload 计量。它不按参数 a 的数值展开接受运行。

## 1. 条件成本定理的准确输入与结论

P 始终是当前 P_direct。假设已有同一 PA 证明系统中的一份固定证明 Π_MP，
结论是以下闭句，且这里 SynImp 采用第 2 节的具体定义：

```text
∀a,u,v,w：
  (SynImp(u,v,w) AND P(a,u) AND P(a,w))
  IMPLIES P(29a+128,v)。                            (1.1)
```

Π_MP 包括一份固定的结构/公理证书；其完整 payload 记 L_Π。
它是本定理的依赖，不能由“标准模型下 MP 保持验收”替代。
若采用另一份同名 SynImp，必须先给出从本文定义到那份前提的固定 PA 推导。

另使用已经逐式证明的基础成本引理：二进制短数词长度为 O(ell(m)+1)，
闭加乘、等式、正反比较及原 exp/length/bit 的短证明编译器，以及固定矩阵的
短 ground 证书构造。后一个引理准确陈述于
[直接确认稿](paper_direct_confirmation_20260905_zh.md) 第 3–4 节：
所有数值全称范围、实际位索引与所有见证的位数有共同界 B 时，固定矩阵的
真实证书可编译为完整 payload≤K(B+1)^e 的 PA 证明。
它不适用于只知道见证数值存在、却没有这些具体界的任意 Sigma-one 公式。

令 |φ|、|ψ| 分别为实际 binaryFormulaCode 的位长，定义

```text
S=1+ell(a)+|φ|+|ψ|，
u=compactFormulaCode(φ)，v=compactFormulaCode(ψ)，
w=compactFormulaCode(NOT φ OR ψ)。
```

**条件成本定理。** 在上述明确依赖下，存在只依赖 Π_MP、固定矩阵和已有编译器
的常数 K,d，以及具体的证明生成算法，对每个 a 和两条合法算术公式 φ、ψ，
输出同一系统的证明

```text
P(nu(a),nu(u)) AND P(nu(a),nu(w))
  IMPLIES P(nu(29a+128),nu(v))，                    (1.2)
```

其完整 payload≤K(S+1)^d。nu 指当前闭的二进制短数词。
因此可取 p3(x,y,z)=K(x+y+z+2)^d，q2(a)=29a+128。
下文证明的是这个条件成本结论，不把尚需验收的 Π_MP 宣告为已有 Lean 定理。
这里 size(phi) 若沿用主稿记号，应取上述实际编码位长，或另有固定多项式支配它
的度量；不计任意大变量号位数的裸节点数不能无说明地代替 |φ|。

## 2. 固定核验关系 SynImp(u,v,w)

### 2.1 参数、表格和根

SynImp 外层存在以下固定个数的数值：三个 public code 的位长 l_u,l_v,l_w，
h、r、两个根索引 α、β，一张元数据表 C、两张正文表 X、Y，以及三个
CanonicalAtWidth 的 token/offset/width/count 参数。要求

```text
lengthDef(l_u,u)，lengthDef(l_v,v)，lengthDef(l_w,w)，
h=1+l_u+l_v+l_w，1≤r≤h，α<r，β<r。
```

C 有 r 行、每行固定 8 个字段；所有字段以位宽 h 读取：

```text
kind, tag, binder, parameter, symbol, left, right, len。
```

kind=0 表示项、kind=1 表示公式，binder≤h，1≤len≤h。
X、Y 各有 r*h 个单元，每单元位宽 h；节点 i 的两个正文分别是

```text
X_i[j]=Row(X,h,i*h+j)，Y_i[j]=Row(Y,h,i*h+j)，j<len_i。
```

X 为原正文，Y 为对应否定正文；项没有逻辑否定，故其 Y 与 X 相同。
要求 ell(C)≤8*r*h，ell(X),ell(Y)≤r*h*h。未用的行尾格可以填 0。
这些位数界不把表格数限制到多项式数值，而只限制实际二进制长度。

所有表读取都可消去为原 compactFixedWidthEntryDef 及有界存在的字段值；
读值的上界可统一取 2^h。这个上界只约束存在见证，不作为枚举范围。
Row 是商余唯一性的定义缩写，不给 PA 添加新的不可解释函数。

### 2.2 每个后序节点的全部构造分支

对每个 i<r 取其 8 个字段，检查下表中的一个有限分支。使用的子节点索引
均严格小于 i，其 kind/binder 另按表要求读取核对。所有未使用字段取 0。

| 分支 | 条件及 X_i | Y_i |
| --- | --- | --- |
| 绑定变量 | kind=0，tag=0，parameter<binder；X_i=[0,parameter] | X_i |
| 自由变量 | kind=0，tag=1；X_i=[1,parameter] | X_i |
| 常量函数 | kind=0，tag=2，parameter=0，symbol=0 或 1；X_i=[2,0,symbol] | X_i |
| 二元函数 | kind=0，tag=2，parameter=2，symbol=0 或 1；两子节点为同 binder 的项；X_i=[2,2,symbol]++X_left++X_right | X_i |
| 正/负关系 | kind=1，tag=0 或 1，parameter=2，symbol=0 或 1；两子节点为同 binder 的项；X_i=[tag,2,symbol]++X_left++X_right | [flip(tag),2,symbol]++X_left++X_right |
| 真/假 | kind=1，tag=2 或 3；X_i=[tag] | [flip(tag)] |
| 合取/析取 | kind=1，tag=4 或 5；两子节点为同 binder 的公式；X_i=[tag]++X_left++X_right | [flip(tag)]++Y_left++Y_right |
| 全称/存在 | kind=1，tag=6 或 7；left 为 binder+1 的公式；X_i=[tag]++X_left | [flip(tag)]++Y_left |

flip 使用实际 NegationTagGraph 的八项表：0↔1、2↔3、4↔5、6↔7。
例如偶数 tag=2p 时取 p<4、mapped=tag+1；奇数 tag=2p+1 时取同一个 p、
tag=mapped+1。这是固定算术析取，而非把外部取否定程序当作一个原子。

上表每个词等式都同时规定 len_i 等于右侧各段长度之和，并对 j<len_i
逐单元比较。固定长度头逐个比较；子段中只读取相应子节点的第 j-offset 项。
减法可写成“存在 t≤h，j=offset+t”，再读取 t，避免截断减法丢失条件。
最多两个子段，所以展开后是一个固定大小、固定量词深度的公式。

字段 parameter 在自由变量分支可以是一个 h 位大数；没有任何“遍历到
parameter”的循环。函数/关系元数只取实际算术语言中的 0 或 2，也不会由
一个大符号码控制重复次数。

两个根 α、β 都要求 kind=1、binder=0。后序节点可共享；严格子索引排除环，
长度的加法等式保证共享时实际展开的正文仍是所记录的真实词。

### 2.3 接到三个真正 public code

对 z=u,v,w，原关系

```text
CanonicalPackedTokenStreamTableauAtWidth
   (z,L_z,A_z,O_z,k_z)
```

作为 SynImp 的合取，另外要求 L_z≤h、k_z≤h，
ell(A_z)≤L_z*k_z，ell(O_z)≤(L_z+1)*k_z。
这些是规范见证本来就满足的界，不改变公开码 z。

用逐项原 CrossEq 连接

```text
u 的 raw token 流 = X_α，v 的 raw token 流 = X_β，
w 的 raw token 流 = [5]++Y_α++X_β。                 (2.1)
```

前两个 count 分别等于 len_α、len_β，第三个 count=1+len_α+len_β。
对 u，例如 X 表的实际区间是 `[α*h,α*h+len_α)`，容量取 r*h，行宽 h；
另一侧为 A_u 的 `[0,L_u)`，容量 L_u，行宽 k_u。复制使用的两表位宽可以不同。
对 w，先单独 TokenCell 读出第 0 项 5，再分别比较两个连续子段。

这三项通过原 sentinel、token 分段和位相等，固定的是实际 compact code，
不是另一个理论上等价的公式编号系统。

### 2.4 给 Π_MP 的统一语法接口

PA 对 i<r 作后序节点归纳。节点字段给变量范围或算术符号的实际有限合法性；
子节点归纳结论和上表拼接式给当前项/公式的合法构造数据。
同时归纳 Y：项原样，公式原子变极性、复合式递归取对偶，得到合法的 NNF 否定
构造数据。两个根因此给 binder=0 的 φ、ψ 数据，(2.1) 给 NOT φ OR ψ 的数据。
具体地，复制同一后序节点表，项的 tag 保持，公式的 tag 取 flip，并把新的
原正文设为 Y_i；原子参数项的 Y=X。这样得到否定词本身的一份正向合法节点表，
而不只是获得一个外部“取否定函数值”的等式。

这里的“数据”就是 [普通 Syntax 基础图](paper_direct_syntax_base_graph_20260905_zh.md)
第 2–3 节的有限节点记录，不需要先从一个 Nat 解码器的正确性取得类型对象。
负词数据与 [否定基础图](paper_direct_negation_base_graph_20260905_zh.md) 第 2 节
的加强归纳相同。后序归纳、Entry 唯一性和规范 packed 编码的 PA 唯一性均是
固定推导，所以这确实能作为 (1.1) 的统一前提接口。

本接口的证明不引用本文 p3 成本结论；故与内部 MP 组装稿引用本节定义之间
不存在“先有短 MP 才能证明其语法前提”的循环。

## 3. 真实 φ、ψ 的具体证书与数值范围

给定两条明确合法公式，按构造树后序列出 φ、ψ 的全部节点，连接成两棵树的
森林。binder 随量词增加；项/公式类别、索引和符号码直接来自其语法构造器。
对每个节点自底向上写 X_i：写固定头、复制至多两条已构造子词；然后按表写
Y_i。复制全过程的单元数≤2*r*h，不能将每一次子词复制都当作只花一步。

当前码的 sentinel 给 ell(u)=|φ|+1、ell(v)=|ψ|+1。
否定的 binaryNat 位长至多翻倍，析取标签占 8 位，所以

```text
ell(w)≤9+2|φ|+|ψ|，h≤12+3|φ|+2|ψ|≤12S。
```

原始 token 每项占至少 2 位；节点数不超过 φ、ψ 的总 token 数，故 r≤h。
每条子词长度≤对应根词长度≤h。初始 binder=0，因此沿语法树出现的 binder≤r≤h。
自由变量号可能数值很大，但其位数已包括在原公式 payload 内，故≤h。

逐个以宽度 h 打包元数据及 r*h 两张词表，得到第 2.1 节的全部位数界。
然后按实际 binaryNatCode 展开 X_α、X_β 和 `[5]++Y_α++X_β`，写三组规范
token/offset 表；每个 offset 是此前各 token 成本 `2ell(token)+2` 的和。
取其真实 payload 和 sentinel，得到三个原 CanonicalAtWidth 的具体见证。
给定 public u、v、w 与这些规范码相同，是语法编码定义及本次逐位构造的等式。

以下粗共同界足够，不追求指数最小：

```text
B=100*(h+1)^4。
```

| 待核验对象 | 当前证书上的界 |
| --- | --- |
| 节点、词内索引的数值全称范围 | r≤h、len≤h |
| C、X、Y 的位数 | ≤8h²、≤h³、≤h³ |
| 词表 Entry 的真实位位置 | `(i*h+j)*h+b < h³` |
| 元数据 Entry 的真实位位置 | `(8i+c)*h+b < 8h²` |
| public token/offset 表的位数 | ≤h²、≤h(h+1) |
| public Tableau、CrossEq 的数值全称范围 | tokenCount≤h；单元位宽≤h；跨表位宽之和≤2h |
| 原 TokenSegment 中的位位置 | ≤payload 宽；即使只用粗界也≤3h² |
| 全部局部数值见证的二进制位数 | ≤B |

最后一行包括所读字段、表格值、payload、sentinel、真实 size、位商余见证和
比较差值。原 exp/bit 原语所需的指数或位索引数值也≤B。
表格数可接近 2^(h³)，但没有任何全称遍历到这个值。

SynImp 展开中读字段/位时只存在量化大值；字长、指数、Entry 位位置作为
短原语实例处理，不朴素展开 lengthDef 或 expDef 的内部数值量词。
这正符合所引用短 ground 矩阵引理的适用条件。

## 4. 从证书到 SynImp 的短 PA 证明

固定 SynImp 的上述算术公式后，令 d_0 为其最大数值全称嵌套深度。
对当前证书逐层生成证明：选择实际成立的节点分支，引入记录的存在值；
对每个实际全称索引核验所需 Entry、词等式、长度和范围条件；最后引回外层
的表格、根、width 和 offset 等见证。

每次原子或原 exp/length/bit 调用的完整 payload≤K_0(B+1)^e_0；
固定深度遍历至多 K_1(B+1)^d_0 次。合取和逐前缀全称合成采用加性的构造：
旧大证明保留一次，逐次追加当前条目的局部证明。于是存在固定 K_2,e_2，

```text
payload(ProofSynImp(u,v,w))≤K_2(B+1)^e_2
                         ≤K_3(S+1)^(4e_2)。        (4.1)
```

代价包含全部结构证书和各大数的二进制短数词。外层存在变量的个数固定；
逐节点存在变量出现在原固定有界全称内，不会把对象公式变成可变元数的新谓词。

这里具体实现的是第 3 节证书的核验及真实 SynImp 闭实例证明，没有使用
“任意 PR 函数的正确值都能短证明”这一未经核算的原则。

## 5. 当前 cut 树上的一次全称实例化

令 Q=∀x B(x)，t 为闭的短数词项，C=B[t]。
当前否定正规形有原语法恒等式

```text
NOT Q = EXISTS x NOT B(x)，(NOT B)[t]=NOT C。
```

第二式由代入与八种 NNF 构造的结构归纳；t 闭，进入量词时其嵌入不改变其
数词正文，也不会捕获任何变量。

以下两节点树证明列表 Γ=[NOT Q,C]：

```text
exs，Gamma=[NOT Q,C]，body=NOT B，witness=t
  closed，Gamma=[NOT C,NOT Q,C]，formula=C。
```

exs 的 body 必须是 binderArity=1 下的 NOT B，witness 是 binderArity=0 的 t。
父列表含 EXISTS(NOT B)=NOT Q；子列表的集合恰为插入 (NOT B)[t]=NOT C 后的
父集合。closed 的两项 C、NOT C 均在其列表，故两节点和证书 `.unary .leaf`
直接满足当前结构规则。

这两个节点的结论是表示蕴含的双元素 sequent。它本身不是单元素列表
`[Q IMPLIES C]`；下面直接把该 sequent 接到 cut，省去不需要的析取封装。

给定 Q 的原证明 D，构造

```text
cut，Gamma=[C]，cutFormula=Q
  wk，Gamma=[Q,C]
    D
  exs，Gamma=[NOT Q,C]，body=NOT B，witness=t
    closed，Gamma=[NOT C,NOT Q,C]，formula=C。
```

cut 的两侧集合分别为 Q::[C]、NOT Q::[C]；wk 包含 D 的结论。
D 和其原证书各出现一次，新增证书是

```text
binary (unary certificate(D)) (unary leaf)。
```

certificate(D) 指本次输入已经携带的那一份证书。四次实例化递归保存它，不在
每次重新调用 certificateOfDerivation 的抽象选择；对应源码可直接用接受任意
既有 baseCertificate 的 specializeCertificate_valid 及其证书增量定理。

对应现有源码的同一构造为
`integration/FoundationCompactDerivationSpecialization.lean:90` 与
`integration/FoundationCompactCertifiedDerivationSpecialization.lean:47`。
这里使用的是 PA 证明系统的外部合法规则及当前载荷编码，不要求 PA 先证明
这份新证明本身被 P 接受；内部证明这种接受性不属于本条外部实例化成本义务。

### 5.1 包括证书的载荷账本

保留上面明确列出的列表，即使个别公式相同也不删除重复项。记 q,c,nb,nq,nc,τ
为 Q、C、NOT B、NOT Q、NOT C、t 的实际 formula/term payload 位长。
按 `FoundationCompactProofTokenMachine.lean:53–88` 的标签和列表头，新增树位数为

```text
50+2q+5c+2nq+nb+nc+τ。
```

四个节点的标签/列表头分别占 14、14、14、8 位。新增结构证书的 binary、
两个 unary、leaf 标签分别占 6、6、6、2 位，合计 20。因此完整新增 payload 为

```text
70+2q+5c+2nq+nb+nc+τ。                              (5.1)
```

数词只占 O(ell(value)+1) 位；NNF 否定至多翻倍。
通用的代入语法界给 (5.1) 关于 |B|+|t|+1 多项式有界。
源码另给同形规范序列版本的界
`192+2048*(|B|+|t|+1)^3`，见 CertifiedDerivationSpecialization 的完整 payload 定理。
本文显式列表可能保留重复项，直接用 (5.1) 和同一代入语法界，必要时扩大常数，
也得“原 payload 加一个固定三次多项式”的界；无需把两个版本的精确常数混同。
这种加性构造不会把原大树复制成指数增长。

## 6. 四次实例化、算术正规化及固定次数组合

对固定 Π_MP 依次用 nu(a)、nu(u)、nu(v)、nu(w) 作第 5 节的实例化。
每次的 body 来自同一个固定对象公式，其数值参数出现次数是固定常数；
代入的是公式码的短数词，而不是把任意公式 φ 的整个语法当作谓词变量替换。

因此四次所得 body 和结论的实际位长均≤K_Π S，各个 witness 项也≤K_Π S。
用第 5.1 节的加性三次界四次，得到

```text
payload(D_instance)≤L_Π+K_4(S+1)^3。               (6.1)
```

其结论仍含项 `29*nu(a)+128`。令 b=29a+128，ell(b)≤ell(a)+8；
已有闭算术原子编译器对固定两次运算生成

```text
29*nu(a)+128=nu(b)
```

的完整 payload 为 poly(ell(a)+1) 的证明。这里常量 29、128 也用同一短数词
项表示。实例化固定的等式代换模板

```text
x=y IMPLIES (P(x,z) IMPLIES P(y,z))
```

即可将最终 P 的 bound 参数改为原目标要求的 nu(b)。模板中 P 的对象公式固定，
其复制次数不随 a 增长。

第 4 节提供 SynImp(nu(u),nu(v),nu(w)) 的短证明。把它与 (6.1)、上述等式
证明及固定逻辑模板组合，消去 SynImp 前提，得到 (1.2)。需要的合取、cut/MP
次数都是固定常数，与 a、φ、ψ 无关。

设每次组合的保守完整成本界为 C(L+H+F+1)^J，所用次数为固定 m。
将 (4.1)、(6.1) 及所有模板实例的多项式界代入，最多将固定指数乘以 J^m。
因 m 固定，仍得到 K(S+1)^d，而不是把 J 次成本沿 a 步运行自我迭代。
K 可以吸收固定 L_Π 及其全部公理/结构证书，但不得依赖本次 a、φ、ψ。

这证明第 1 节的条件成本定理。q2(a)=29a+128 已处处≥a+1，不另需参数相关的
上界抬高程序。

## 7. 结论的依赖边界

本文已具体闭合：SynImp 的有限语法/取否定/拼接/真实 bit 编码证书，全部
ground 全称范围与大整数位数界，原矩阵短证书调用，正确 NNF 的 exs/closed
全称实例化，完整 tree+certificate 成本和四次实例化后的固定多项式 p3。

仍明确保留的主要依赖是一份采用第 2 节 SynImp 的固定同系统 Π_MP。
其构造应由 [新增 MP 节点稿](paper_direct_mp_new_nodes_20260905_zh.md) 与各个
已展开的矩阵输运、来源及基础图引理完成，并单独审查统一量词、同一 P 和
29a+128 计量。本文不通过重复这些内部推导来证明自身的依赖。

一旦 Π_MP 在纸面验收通过，所需短实例成本不再另依赖关于 a 的短运行轨迹，
也不需要对 P 作反射；第 1 节即把该固定定理提升为条件 (3) 要求的 p3 界。
本稿没有改变条件 (1)、条件 (2) 或无界数论有效向量的状态。
