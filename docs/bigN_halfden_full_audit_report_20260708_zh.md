# big-N half-denominator 审计报告（已由 clean route 取代主线）

日期：2026-07-08

本文件保留 half-denominator route 的审计结论，但不再作为投稿主审计文件。
当前投稿主审计文件为：

```text
docs/clean_submission_route_audit_20260708_zh.md
```

## 关键结论

旧 half-denominator formula-level endpoints 仍然依赖：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

因此，旧公式路线不能作为本轮投稿主 theorem。为了最大化论文信用，本轮主线
已经切换到 clean checker/collision theorem：

```lean
cleanUpperProvider_submissionRoute
```

所在文件：

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

该 theorem 的 axiom profile 为：

```text
[propext, Classical.choice, Quot.sound]
```

未出现上述三个项目级依赖。

## 处理原则

half-denominator 精细公式

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

保留为后续 clean upstream provider 构造目标。本轮投稿只使用已经审计干净的
`N = max upperN threshold` 碰撞路线。

详见：

```text
docs/clean_submission_route_audit_20260708_zh.md
```
