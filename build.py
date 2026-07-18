#!/usr/bin/env python3
"""Dependency-free static site generator: problems/ + attempts/ -> site/.

Python 3 stdlib only. Markdown subset: #-#### headings, paragraphs, -/* and
numbered lists, > blockquotes, ``` fenced code, | tables, **bold**, *italic*,
`code`, [text](url), horizontal rules. $...$ / $$...$$ are passed through
untouched for MathJax.
"""
import html
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).parent
SITE = ROOT / "site"

STATUS_LABELS = {"open": "open", "partially-solved": "partially solved", "solved": "solved"}


def fail(msg):
    sys.exit(f"build error: {msg}")


def parse_frontmatter(path):
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        fail(f"{path}: missing frontmatter")
    try:
        _, fm, body = text.split("---", 2)
    except ValueError:
        fail(f"{path}: unterminated frontmatter")
    meta = {}
    for line in fm.strip().splitlines():
        if not line.strip() or line.strip().startswith("#"):
            continue
        if ":" not in line:
            fail(f"{path}: bad frontmatter line: {line!r}")
        key, _, val = line.partition(":")
        val = val.strip()
        if val.startswith("[") and val.endswith("]"):
            val = [v.strip() for v in val[1:-1].split(",") if v.strip()]
        meta[key.strip()] = val
    return meta, body.strip()


# ---------------------------------------------------------------- markdown

def _protect(body, store):
    def stash(m):
        store.append(m.group(0))
        return f"\x00{len(store) - 1}\x00"

    body = re.sub(r"```.*?```", stash, body, flags=re.S)      # fenced code
    body = re.sub(r"\$\$.*?\$\$", stash, body, flags=re.S)    # display math
    body = re.sub(r"(?<!\$)\$(?!\$).+?(?<!\$)\$(?!\$)", stash, body)  # inline math
    body = re.sub(r"`[^`\n]+`", stash, body)                  # inline code
    return body


def _restore(text, store):
    def unstash(m):
        raw = store[int(m.group(1))]
        if raw.startswith("```"):
            code = raw.strip("`\n")
            code = code.split("\n", 1)[1] if "\n" in code else ""
            return f"<pre><code>{html.escape(code)}</code></pre>"
        if raw.startswith("`"):
            return f"<code>{html.escape(raw[1:-1])}</code>"
        return html.escape(raw)  # math: escaped text, MathJax reads DOM text

    return re.sub(r"\x00(\d+)\x00", unstash, text)


def _inline(text):
    text = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)", r'<a href="\2">\1</a>', text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"(?<!\*)\*([^*\n]+)\*(?!\*)", r"<em>\1</em>", text)
    return text


def md_to_html(body):
    store = []
    body = _protect(body, store)
    body = html.escape(body, quote=False)
    out, i = [], 0
    lines = body.split("\n")
    n = len(lines)
    while i < n:
        line = lines[i]
        s = line.strip()
        if not s:
            i += 1
            continue
        if re.fullmatch(r"-{3,}", s):
            out.append("<hr>")
            i += 1
        elif s.startswith("#"):
            level = len(s) - len(s.lstrip("#"))
            out.append(f"<h{level}>{_inline(s[level:].strip())}</h{level}>")
            i += 1
        elif s.startswith("|"):
            rows = []
            while i < n and lines[i].strip().startswith("|"):
                cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
                if not all(re.fullmatch(r":?-+:?", c) for c in cells):
                    rows.append(cells)
                i += 1
            thead = "".join(f"<th>{_inline(c)}</th>" for c in rows[0])
            tbody = "".join(
                "<tr>" + "".join(f"<td>{_inline(c)}</td>" for c in r) + "</tr>"
                for r in rows[1:]
            )
            out.append(
                f'<div class="tablewrap"><table><thead><tr>{thead}</tr></thead>'
                f"<tbody>{tbody}</tbody></table></div>"
            )
        elif s.startswith("&gt;"):
            quote = []
            while i < n and lines[i].strip().startswith("&gt;"):
                quote.append(lines[i].strip()[4:].strip())
                i += 1
            out.append(f"<blockquote><p>{_inline(' '.join(quote))}</p></blockquote>")
        elif re.match(r"^[-*] ", s) or re.match(r"^\d+\. ", s):
            ordered = bool(re.match(r"^\d+\. ", s))
            start = int(re.match(r"^(\d+)\. ", s).group(1)) if ordered else 1
            items, current = [], None
            pat = r"^\d+\. " if ordered else r"^[-*] "
            while i < n:
                ls = lines[i].strip()
                if re.match(pat, ls):
                    if current is not None:
                        items.append(current)
                    current = re.sub(pat, "", ls)
                elif ls and lines[i].startswith((" ", "\t")):
                    current += " " + ls  # continuation line
                else:
                    break
                i += 1
            items.append(current)
            tag = "ol" if ordered else "ul"
            attr = f' start="{start}"' if ordered and start != 1 else ""
            out.append(
                f"<{tag}{attr}>" + "".join(f"<li>{_inline(it)}</li>" for it in items) + f"</{tag}>"
            )
        else:
            para = []
            while i < n and lines[i].strip() and not re.match(
                r"^(#|\||&gt;|[-*] |\d+\. |-{3,}$)", lines[i].strip()
            ):
                para.append(lines[i].strip())
                i += 1
            out.append(f"<p>{_inline(' '.join(para))}</p>")
    return _restore("\n".join(out), store)


# ---------------------------------------------------------------- templates

MATHJAX = (
    '<script>MathJax={tex:{inlineMath:[["$","$"],["\\\\(","\\\\)"]]}};</script>'
    '<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>'
)


def page(title, body_html, depth=0):
    rel = "../" * depth
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<link rel="stylesheet" href="{rel}style.css">
{MATHJAX}
</head>
<body>
<header><a href="{rel}index.html">Open Problems in Information Theory</a></header>
<main>
{body_html}
</main>
<footer>Maintained on <a href="https://github.com/gokhanmergen/information-theory-problems">GitHub</a> — problems, corrections, and attempts (human or AI) welcome by pull request.</footer>
</body>
</html>
"""


def badge(status):
    label = STATUS_LABELS.get(status, status)
    return f'<span class="badge badge-{html.escape(status)}">{html.escape(label)}</span>'


def load_attempts(problem_id):
    adir = ROOT / "attempts" / problem_id
    if not adir.is_dir():
        return []
    attempts = []
    for f in sorted(adir.glob("*.md")):
        meta, body = parse_frontmatter(f)
        if meta.get("problem") != problem_id:
            fail(f"{f}: frontmatter problem={meta.get('problem')!r} != dir {problem_id!r}")
        attempts.append((f.name, meta, body))
    return attempts


def main():
    problems = []
    for f in sorted((ROOT / "problems").glob("*.md")):
        meta, body = parse_frontmatter(f)
        for key in ("id", "title", "status"):
            if key not in meta:
                fail(f"{f}: missing frontmatter key {key!r}")
        if meta["id"] != f.stem:
            fail(f"{f}: id {meta['id']!r} != filename stem")
        problems.append((meta, body, load_attempts(meta["id"])))

    if SITE.exists():
        shutil.rmtree(SITE)
    (SITE / "problems").mkdir(parents=True)
    shutil.copy(ROOT / "static" / "style.css", SITE / "style.css")

    # index
    rows = []
    for meta, _, attempts in problems:
        tags = " ".join(f'<span class="tag">{html.escape(t)}</span>' for t in meta.get("tags", []))
        posed = html.escape(meta.get("posed_year", ""))
        att = f'{len(attempts)} attempt{"s" if len(attempts) != 1 else ""}' if attempts else "no attempts yet"
        rows.append(
            f'<a class="card" href="problems/{meta["id"]}.html">'
            f'<div class="card-top"><h2>{html.escape(meta["title"])}</h2>{badge(meta["status"])}</div>'
            f'<div class="card-meta">{f"posed {posed} · " if posed else ""}{att}</div>'
            f'<div class="tags">{tags}</div></a>'
        )
    n_open = sum(1 for m, _, _ in problems if m["status"] != "solved")
    intro = (
        "<h1>Open Problems in Information Theory</h1>"
        f"<p class='lede'>A community-curated list of {n_open} open problems, in the spirit of "
        '<a href="https://www.erdosproblems.com/">erdosproblems.com</a>. '
        "Humans and AI agents attempt problems under a common protocol; every attempt is "
        "a reviewable, versioned record of what was tried, what was proved, and what failed. "
        'Contribute on GitHub.</p>'
    )
    (SITE / "index.html").write_text(page("Open Problems in Information Theory",
                                          intro + "\n".join(rows)), encoding="utf-8")

    # problem pages
    for meta, body, attempts in problems:
        parts = [
            f'<div class="card-top"><h1>{html.escape(meta["title"])}</h1>{badge(meta["status"])}</div>'
        ]
        posed_by, posed_year = meta.get("posed_by", ""), meta.get("posed_year", "")
        if posed_by or posed_year:
            parts.append(
                f'<p class="provenance">Posed by {html.escape(posed_by)}'
                f'{f", {html.escape(posed_year)}" if posed_year else ""}.</p>'
            )
        parts.append(md_to_html(body))
        parts.append(f"<h2>Attempts ({len(attempts)})</h2>")
        if not attempts:
            parts.append('<p class="muted">No attempts recorded yet. See AGENTS.md in the repository for the attempt protocol.</p>')
        for name, ameta, abody in attempts:
            head = (
                f'<span class="att-who">{html.escape(ameta.get("attempter", "?"))}</span> '
                f'<span class="muted">{html.escape(ameta.get("date", ""))}'
                f'{" · " + html.escape(ameta["model"]) if ameta.get("model") else ""}</span> '
                f'<span class="tag">{html.escape(ameta.get("type", ""))}</span> '
                f'<span class="tag tag-status">{html.escape(ameta.get("status", ""))}</span>'
            )
            parts.append(
                f'<details class="attempt"><summary>{head}</summary>'
                f'<div class="attempt-body">{md_to_html(abody)}'
                f'<p class="muted">source: attempts/{html.escape(meta["id"])}/{html.escape(name)}</p>'
                f"</div></details>"
            )
        (SITE / "problems" / f'{meta["id"]}.html').write_text(
            page(meta["title"], "\n".join(parts), depth=1), encoding="utf-8"
        )

    print(f"built site/ — {len(problems)} problems, "
          f"{sum(len(a) for _, _, a in problems)} attempts")


if __name__ == "__main__":
    main()
