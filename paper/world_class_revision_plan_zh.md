# 世界级论文改造规划单

日期：2026-07-08

工作副本：

```text
/home/james/code/sondow-pudlak-bigN-audit-20260708/sondow-pudlak-collision-box-bigN-halfden-full-20260708
```

基准 release：

```text
bigN-halfden-full-20260708
```

基准 commit：

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

## 当前投稿策略

本轮投稿不追求精确 half-denominator 公式级大 `N`，也不追求十进制数值 `N`。
本轮目标是把已经审计干净的 proof-level/collision-level 结果整理成可信论文。

主 Lean theorem：

```lean
cleanUpperProvider_submissionRoute
```

主文件：

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

主数学内容：

```lean
N = max upperN threshold
```

并且同一路线推出：

```lean
¬ is_rational euler_mascheroni
```

## 论文信用原则

论文信用优先于公式外观。旧 half-denominator formula route 虽然有漂亮形式：

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

但现有 endpoints 的 axiom profile 仍含：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

因此本轮不得把旧公式路线作为主 theorem。正确策略是：

1. 主文使用 clean `max upperN threshold` collision theorem。
2. 清楚说明 axiom profile 已经清除三个项目级依赖。
3. 把 formula-level half-denominator upper provider 和 numerical extraction
   写成后续 refinement。
4. 不声称无条件证明 Euler-Mascheroni 常数无理性。

## 已完成交付物

1. 新增 clean Lean 入口：

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

2. 新增 clean 审计报告：

```text
docs/clean_submission_route_audit_20260708_zh.md
```

3. 重写 README 和 STATUS，使仓库首页指向 clean route。
4. 重写英文投稿稿：

```text
paper/submission_bigN_formal_manuscript_en.md
```

5. 同步中英文草稿：

```text
paper/paper_new_en.md
paper/paper_new_zh.md
```

6. 更新复现日志：

```text
docs/bigN_validation_log_20260708_zh.md
```

## 验证门槛

本轮提交前必须通过：

```bash
lake build integration.SondowProjectBigNCleanSubmissionRoute
git diff --check
```

并确认：

```lean
#print axioms cleanUpperProvider_submissionRoute
```

输出仅为：

```text
[propext, Classical.choice, Quot.sound]
```

## 后续工作

后续另起阶段处理：

1. clean upstream half-denominator upper provider；
2. formula-level `17 * max 3 ((rat.q.den + 1) / 2) + 8`；
3. decimal numerical `N` extraction；
4. 正式期刊 LaTeX 排版和参考文献完善；
5. 目标期刊适配，包括《数学进展》、北京大学学报自然科学版或更高端英文数学期刊。
