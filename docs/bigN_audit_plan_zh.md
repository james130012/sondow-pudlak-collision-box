# big-N 投稿路线规划单

日期：2026-07-08

## 当前目标

本轮目标不是数值级 `N`，也不是 half-denominator 精细公式级 `N`。当前目标是
形成一个审计干净、可投稿表述的 Lean-checked collision theorem。

主 theorem：

```lean
cleanUpperProvider_submissionRoute
```

主文件：

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

主结论：

```lean
N = max upperN threshold
```

并且同一路线推出：

```lean
¬ is_rational euler_mascheroni
```

## 已完成

1. 在 release `bigN-halfden-full-20260708` 上建立隔离审计 workspace。
2. 确认旧 half-den formula-level route 仍含三个项目级依赖。
3. 新增 clean submission route 文件。
4. 构建 `integration.SondowProjectBigNCleanSubmissionRoute` 成功。
5. 对 clean route theorem 运行 `#print axioms`。
6. 确认主 theorem 不含：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

## 投稿主线

论文应围绕以下链条展开：

1. clean upper provider 给出 upper tail 与 cutoff `upperN`。
2. clean tail-gap certificate 给出同一 measured route 的 threshold。
3. Lean 中 rational branch 的 computed collision number 等于
   `max upperN threshold`。
4. upper inequality 与 lower strict gap 在同一 computed `N` 处冲突。
5. 因而 clean route 推出 `¬ is_rational euler_mascheroni`。

## 后续工作

后续另开工作处理：

1. clean upstream half-denominator upper provider；
2. 公式级

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

3. decimal numerical `N` extraction；
4. 更细的 theorem compression 和论文排版。

这些工作不阻塞当前 clean proof-level/collision-level 投稿版本。
