from pathlib import Path
import html
import re
import shutil
import subprocess
import tempfile
import urllib.request

import markdown
from weasyprint import HTML

root = Path(__file__).resolve().parents[1]
out = root / 'generated'
out.mkdir(exist_ok=True)

zh = (root / 'paper_new_zh.md').read_text(encoding='utf-8')
en = (root / 'paper_new_en.md').read_text(encoding='utf-8')

KATEX_CSS_URL = 'https://cdn.jsdelivr.net/npm/katex@0.16.10/dist/katex.min.css'
KATEX_CSS_PATH = out / 'katex.min.css'
PAPER_TITLE_ZH = 'Lean 检查的 Sondow-Pudlak 存在性大 N 证书'
PAPER_KICKER = 'Lean-checked existential big-N certificate'
PAPER_META = (
    '本地导出自 <code>paper_new_zh.md</code> / <code>paper_new_en.md</code>，'
    '公式由 KaTeX 渲染，适配 A4 审计版式。'
)


def ensure_katex_css() -> None:
    if KATEX_CSS_PATH.exists():
        return
    npx_cache = Path.home() / '.npm' / '_npx'
    cached = sorted(
        (p for p in npx_cache.glob('*/node_modules/katex/dist/katex.min.css') if p.is_file()),
        key=lambda p: p.stat().st_mtime,
        reverse=True
    )
    if cached:
        shutil.copy2(cached[0], KATEX_CSS_PATH)
        return
    with urllib.request.urlopen(KATEX_CSS_URL) as resp:
        KATEX_CSS_PATH.write_bytes(resp.read())


_formula_cache: dict[str, str] = {}


def render_katex_display(math_text: str) -> str:
    cached = _formula_cache.get(math_text)
    if cached is not None:
        return cached

    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / 'formula.tex'
        src.write_text(math_text, encoding='utf-8')
        proc = subprocess.run(
            ['npx', '--yes', 'katex', '-i', str(src), '-F', 'html', '--display-mode'],
            capture_output=True,
            text=True
        )

    if proc.returncode != 0:
        escaped = html.escape(proc.stderr.strip() or proc.stdout.strip() or 'KaTeX render failed')
        result = f'<div class="math-error" title="{escaped}"><pre>{html.escape(math_text)}</pre></div>'
    else:
        rendered = proc.stdout.strip()
        if rendered:
            result = f'<div class="math-block">{rendered}</div>'
        else:
            result = '<div class="math-error">[empty formula]</div>'

    _formula_cache[math_text] = result
    return result


def extract_math_fences(text: str):
    blocks: list[str] = []

    def repl(m: re.Match[str]) -> str:
        idx = len(blocks)
        blocks.append(m.group(1).strip('\n'))
        return f'<div class="math-placeholder" data-math-index="{idx}"></div>'

    converted = re.sub(r'```math\n(.*?)\n```', repl, text, flags=re.S)
    return converted, blocks


def md_to_html(text: str) -> str:
    text, blocks = extract_math_fences(text)
    rendered = markdown.markdown(
        text,
        extensions=['extra', 'sane_lists'],
        output_format='html5',
    )
    for i, formula in enumerate(blocks):
        rendered = rendered.replace(
            f'<div class="math-placeholder" data-math-index="{i}"></div>',
            render_katex_display(formula)
        )
    return rendered


def paper_wrapper(inner_html: str, subtitle: str, with_cover: bool = True) -> str:
    ensure_katex_css()
    cover = f'''
    <section class="cover">
      <div class="kicker">{PAPER_KICKER}</div>
      <h1 class="title">{PAPER_TITLE_ZH}</h1>
      <div class="subtitle">{subtitle}</div>
      <div class="meta">{PAPER_META}</div>
    </section>
    '''
    body = inner_html if not with_cover else cover + inner_html
    return f'''<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{PAPER_TITLE_ZH}</title>
<link rel="stylesheet" href="katex.min.css">
<style>
  @page {{
    size: A4;
    margin: 22mm 18mm 18mm 18mm;
  }}
  :root {{
    --ink: #121418;
    --muted: #4d5966;
    --accent: #882e1e;
    --rule: #d6cdb7;
    --paper: #fffdf8;
  }}
  * {{ box-sizing: border-box; }}
  body {{
    margin: 0;
    background: var(--paper);
    color: var(--ink);
    font-family: "Noto Serif CJK SC", "Noto Serif", "Times New Roman", serif;
    font-size: 10.7pt;
    line-height: 1.72;
    text-rendering: optimizeLegibility;
  }}
  main {{
    max-width: 100%;
  }}
  .cover {{
    border: 1.2pt solid var(--rule);
    padding: 25mm 18mm;
    margin-bottom: 12mm;
    page-break-after: always;
    background: linear-gradient(135deg, #fffcf5 0%, #fffdf8 100%);
  }}
  .kicker {{
    color: var(--accent);
    font-size: 9.8pt;
    font-weight: 700;
    letter-spacing: .14em;
    text-transform: uppercase;
    margin-bottom: 12mm;
  }}
  .title {{
    font-family: "Noto Sans CJK SC", "Noto Sans", sans-serif;
    font-size: 29pt;
    line-height: 1.2;
    letter-spacing: 0.01em;
    margin: 0 0 10mm;
  }}
  .subtitle {{
    color: var(--muted);
    font-size: 12.4pt;
    line-height: 1.6;
    max-width: 94%;
  }}
  .meta {{
    margin-top: 22mm;
    color: var(--muted);
    border-top: 1pt solid var(--rule);
    padding-top: 6mm;
    font-size: 9.4pt;
  }}
  h1, h2, h3, h4 {{
    font-family: "Noto Sans CJK SC", "Noto Sans", sans-serif;
    color: #0f1114;
    line-height: 1.28;
    page-break-after: avoid;
  }}
  h1 {{
    font-size: 21.5pt;
    margin: 0 0 8mm;
    padding-bottom: 4mm;
    border-bottom: 1.2pt solid var(--rule);
  }}
  h2 {{
    font-size: 16pt;
    margin: 14mm 0 5mm;
  }}
  h3 {{
    font-size: 12.9pt;
    margin: 9mm 0 4mm;
  }}
  p {{ margin: 0 0 4mm; text-align: justify; }}
  ul, ol {{
    padding-left: 8mm;
    margin: 0 0 4mm;
  }}
  li {{ margin: 1.4mm 0; }}
  code {{
    font-family: "Fira Code", "JetBrains Mono", "Noto Sans Mono CJK SC", monospace;
    background: #f6f2ea;
    border: 0.4pt solid #e3ddcf;
    padding: 0.2mm 0.8mm;
    border-radius: 2mm;
    font-size: 9.1pt;
  }}
  pre {{
    background: #f7f3eb;
    border: 0.8pt solid #ddd6c8;
    border-left: 3pt solid var(--accent);
    padding: 3.4mm;
    border-radius: 2mm;
    overflow: hidden;
    white-space: pre-wrap;
    page-break-inside: avoid;
    margin: 4mm 0;
  }}
  pre code {{
    border: 0;
    padding: 0;
    background: transparent;
    font-size: 8.6pt;
  }}
  .math-block, .math-placeholder {{
    page-break-inside: avoid;
    margin: 4mm 0;
  }}
  .katex {{
    font-size: 1.12em;
  }}
  .math-error {{
    border: 0.8pt dashed #b03b3b;
    color: #7c2323;
    background: #fff0f0;
    padding: 2mm;
    border-radius: 2mm;
  }}
  table {{
    border-collapse: collapse;
    width: 100%;
    margin: 5mm 0;
  }}
  th, td {{
    border: 0.5pt solid var(--rule);
    padding: 2mm;
    vertical-align: top;
  }}
  th {{
    background: #f2ebdf;
  }}
  hr {{ border: 0; border-top: 0.9pt solid var(--rule); margin: 12mm 0; }}
</style>
</head>
<body>
<main>
  {body}
</main>
</body>
</html>
'''


zh_html = md_to_html(zh)
en_html = md_to_html(en)

zh_doc = paper_wrapper(
    f'<article class="paper-section">{zh_html}</article>',
    '中文正文版本，聚焦存在性大 N 定理、真实根输入与后续数值路线。'
)
zh_path = out / 'paper_new_zh.html'
zh_path.write_text(zh_doc, encoding='utf-8')
pdf_path = out / 'paper_new_zh.pdf'
HTML(filename=str(zh_path)).write_pdf(str(pdf_path), optimize_size=('fonts', 'images'))

combined_doc = paper_wrapper(
    f'''
    <article class="paper-section">{zh_html}</article>
    <article class="paper-section">{en_html}</article>
    ''',
    '中文正文 + English full paper，面向存在性大 N checkpoint 审计。'
)
combined_path = out / 'sondow_pudlak_bigN_existence_paper_zh_en.html'
combined_pdf_path = out / 'sondow_pudlak_bigN_existence_paper_zh_en.pdf'
combined_path.write_text(combined_doc, encoding='utf-8')
HTML(filename=str(combined_path)).write_pdf(
    str(combined_pdf_path),
    optimize_size=('fonts', 'images')
)

# Keep the historical artifact names fresh as aliases so old download links do
# not point at stale paper content.
legacy_combined_path = out / 'euler_gamma_collision_paper_zh_en.html'
legacy_combined_pdf_path = out / 'euler_gamma_collision_paper_zh_en.pdf'
shutil.copy2(combined_path, legacy_combined_path)
shutil.copy2(combined_pdf_path, legacy_combined_pdf_path)

print(zh_path)
print(pdf_path)
print(combined_path)
print(combined_pdf_path)
print(legacy_combined_path)
print(legacy_combined_pdf_path)
