# 中文主稿 PDF 生成与检查报告

生成时间：2026-07-09 00:09 CST

## 文件

- Markdown 源文：`paper/submission_bigN_formal_manuscript_zh.md`
- PDF 排版 Markdown：`paper/submission_bigN_formal_manuscript_zh_print.md`
- Pandoc LaTeX：`paper/submission_bigN_formal_manuscript_zh.tex`
- PDF：`paper/submission_bigN_formal_manuscript_zh.pdf`

## 生成方式

PDF 由 Markdown 经 Pandoc + Tectonic 直接生成，没有走 HTML。

使用的关键设置：

```text
documentclass=ctexart
papersize=a4
classoption=12pt
geometry=margin=22mm
mainfont=Noto Serif
sansfont=Noto Sans
monofont=DejaVu Sans Mono
CJKmainfont=Noto Serif CJK SC
CJKsansfont=Noto Sans CJK SC
```

## Markdown 完整性检查

```text
nonspace_chars: 4545
bytes: 7320
h2_count: 8
dollar_count_even: True
forbidden_delims: False
```

疑似截断/占位检查：

```text
TODO|待补|未完|未完待续|这里省略|后续补充|...|…… : no matches
```

投稿稿没有加入可见的 `【正文完】` 标记；完整性用 Markdown 尾部和 PDF 文本尾部
共同核对。二者均以“参考文献”完整结束。

## PDF 检查

```text
Pages: 6
Page size: 595.28 x 841.89 pts (A4)
File size: 130527 bytes
Encrypted: no
PDF version: 1.5
```

LaTeX 文件检查：

```text
contains_documentclass: True
has_end_document: True
tex_bytes: 15325
```

Tectonic 编译结果：

```text
missing-character warnings: none
overfull hbox warnings: none
underfull hbox warnings: present, non-fatal
absolute font path reproducibility warnings: present, non-fatal
```

PDF 文本尾部已用 `pdftotext` 检查，能看到第 6 节结论和完整参考文献列表。
