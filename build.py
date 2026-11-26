#!/usr/bin/env python3
"""Dependency-free static site generator: problems/ + lean/ + attempts/ -> site/.

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
LEAN_SOLUTIONS_DIR = ROOT / "lean" / "InfoTheory" / "Solutions"

STATUS_LABELS = {
    "open": "open",
    "partially-solved": "partially solved",
    "solved": "solved",
}

CATEGORY_LABELS = {
    "entropy-inequalities": "Entropy Inequalities & Geometry",
    "channel-capacity": "Channel Capacity & Synchronization",
    "network-info-theory": "Network Information Theory",
    "source-coding": "Source Coding & Compression",
    "zero-error": "Zero-Error & Graph Capacity",
    "coding-theory": "Coding Theory & Bounds",
    "network-coding": "Network Coding & Storage",
    "quantum-info": "Quantum Information Theory",
    "security-privacy": "Security, Privacy & Secrecy",
    "statistical-info-theory": "Statistical Info Theory & Testing",
}


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

FILTER_JS = """<script>
(function(){
  const q = document.getElementById('search');
  const cards = Array.from(document.querySelectorAll('.card'));
  const countEl = document.getElementById('match-count');
  let activeCat = 'all', activeStatus = 'all';

  function apply(){
    const term = (q.value || '').trim().toLowerCase();
    let shown = 0;
    for (const c of cards){
      const okCat = activeCat === 'all' || c.dataset.cat === activeCat;
      const okSt = activeStatus === 'all' || c.dataset.status === activeStatus;
      const okQ = !term || c.dataset.search.includes(term);
      const show = okCat && okSt && okQ;
      c.style.display = show ? '' : 'none';
      if (show) shown++;
    }
    if (countEl) countEl.textContent = shown + ' of ' + cards.length + ' problems shown';
  }

  document.querySelectorAll('[data-filter-cat]').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('[data-filter-cat]').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      activeCat = btn.dataset.filterCat;
      apply();
    });
  });

  document.querySelectorAll('[data-filter-status]').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('[data-filter-status]').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      activeStatus = btn.dataset.filterStatus;
      apply();
    });
  });

  if (q) q.addEventListener('input', apply);
  apply();
})();
</script>"""


def page(title, body_html, depth=0, extra_js=""):
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
<header>
  <a href="{rel}index.html">Open Problems in Information Theory</a>
  <span class="header-note">Lean 4 Verified Problem Platform</span>
</header>
<main>
{body_html}
</main>
<footer>Maintained on <a href="https://github.com/gokhanmergen/information-theory-problems">GitHub</a> — problems, Lean 4 formalizations, corrections, and proofs (human or AI) welcome by pull request.</footer>
{extra_js}
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


def load_lean_info(meta):
    lean_file = meta.get("lean_file", "")
    lean_module = meta.get("lean_module", "")
    if not lean_file:
        return None
    p = ROOT / lean_file
    if not p.is_file():
        fail(f"{meta['id']}: lean_file {lean_file!r} does not exist")
    short_mod = lean_module.split(".")[-1] if lean_module else p.stem
    sol_file = LEAN_SOLUTIONS_DIR / f"{short_mod}.lean"
    return {
        "file": lean_file,
        "module": lean_module,
        "code": p.read_text(encoding="utf-8").strip(),
        "has_solution": sol_file.is_file(),
        "solution_file": f"lean/InfoTheory/Solutions/{short_mod}.lean",
    }


def main():
    problems = []
    for f in sorted((ROOT / "problems").glob("*.md")):
        meta, body = parse_frontmatter(f)
        for key in ("id", "title", "status"):
            if key not in meta:
                fail(f"{f}: missing frontmatter key {key!r}")
        if meta["id"] != f.stem:
            fail(f"{f}: id {meta['id']!r} != filename stem")
        lean_info = load_lean_info(meta)
        problems.append((meta, body, load_attempts(meta["id"]), lean_info))

    if SITE.exists():
        shutil.rmtree(SITE)
    (SITE / "problems").mkdir(parents=True)
    shutil.copy(ROOT / "static" / "style.css", SITE / "style.css")

    # Stats
    n_total = len(problems)
    n_open = sum(1 for m, _, _, _ in problems if m["status"] in ("open", "partially-solved"))
    n_solved = sum(1 for m, _, _, _ in problems if m["status"] == "solved")
    n_lean = sum(1 for _, _, _, l in problems if l is not None)
    n_lean_sol = sum(1 for _, _, _, l in problems if l is not None and l["has_solution"])

    # Category counts
    cat_counts = {}
    for m, _, _, _ in problems:
        c = m.get("category", "uncategorized")
        cat_counts[c] = cat_counts.get(c, 0) + 1

    # Index cards
    rows = []
    for meta, _, attempts, lean_info in problems:
        cat = meta.get("category", "uncategorized")
        cat_label = CATEGORY_LABELS.get(cat, cat)
        tags = " ".join(f'<span class="tag">{html.escape(t)}</span>' for t in meta.get("tags", []))
        posed = html.escape(meta.get("posed_year", ""))
        att = f'{len(attempts)} attempt{"s" if len(attempts) != 1 else ""}' if attempts else "no attempts yet"
        lean_badge = ""
        if lean_info:
            if lean_info["has_solution"]:
                lean_badge = '<span class="badge badge-lean-verified">Lean 4 proof</span>'
            else:
                lean_badge = '<span class="badge badge-lean">Lean 4</span>'
        search_blob = " ".join([
            meta["id"], meta["title"], meta.get("posed_by", ""),
            cat, cat_label, " ".join(meta.get("tags", []))
        ]).lower()
        rows.append(
            f'<a class="card" href="problems/{meta["id"]}.html" '
            f'data-cat="{html.escape(cat)}" data-status="{html.escape(meta["status"])}" '
            f'data-search="{html.escape(search_blob)}">'
            f'<div class="card-top"><h2>{html.escape(meta["title"])}</h2>'
            f'<div class="badges">{lean_badge}{badge(meta["status"])}</div></div>'
            f'<div class="card-meta">{html.escape(cat_label)} · '
            f'{f"posed {posed} · " if posed else ""}{att}</div>'
            f'<div class="tags">{tags}</div></a>'
        )

    cat_buttons = ['<button class="pill active" data-filter-cat="all">All (' + str(n_total) + ')</button>']
    for cat_key, cat_label in CATEGORY_LABELS.items():
        if cat_key in cat_counts:
            cat_buttons.append(
                f'<button class="pill" data-filter-cat="{html.escape(cat_key)}">'
                f'{html.escape(cat_label)} ({cat_counts[cat_key]})</button>'
            )

    status_buttons = [
        '<button class="pill active" data-filter-status="all">All statuses</button>',
        '<button class="pill" data-filter-status="open">Open</button>',
        '<button class="pill" data-filter-status="partially-solved">Partially solved</button>',
        '<button class="pill" data-filter-status="solved">Solved</button>',
    ]

    intro = (
        "<h1>Open Problems in Information Theory</h1>"
        f"<p class='lede'>A curated, Lean 4–formalized catalog of <strong>{n_open} open problems</strong> "
        f"({n_total} total, {n_lean} with machine-checked Lean 4 statements), in the spirit of "
        '<a href="https://www.erdosproblems.com/">erdosproblems.com</a>. '
        "Provability comes for free via Lean: submit a proof of <code>Statement</code> (or "
        "<code>¬ Statement</code>) under <code>lean/InfoTheory/Solutions/</code> and run "
        "<code>python3 scripts/verify_proof.py --verify &lt;id&gt;</code>.</p>"
        '<div class="stats">'
        f'<div class="stat"><span class="stat-num">{n_open}</span><span class="stat-lbl">Open / Partial</span></div>'
        f'<div class="stat"><span class="stat-num">{n_lean}</span><span class="stat-lbl">Lean 4 Statements</span></div>'
        f'<div class="stat"><span class="stat-num">{n_solved}</span><span class="stat-lbl">Solved</span></div>'
        f'<div class="stat"><span class="stat-num">{n_lean_sol}</span><span class="stat-lbl">Lean Verified</span></div>'
        '</div>'
        '<div class="controls">'
        '<input id="search" type="search" placeholder="Search problems by title, author, tag, or subfield…">'
        f'<div class="pill-row">{"".join(status_buttons)}</div>'
        f'<div class="pill-row">{"".join(cat_buttons)}</div>'
        '<div id="match-count" class="match-count"></div>'
        '</div>'
    )
    (SITE / "index.html").write_text(
        page("Open Problems in Information Theory", intro + "\n".join(rows), extra_js=FILTER_JS),
        encoding="utf-8",
    )

    # Problem pages
    for meta, body, attempts, lean_info in problems:
        lean_badge = ""
        if lean_info:
            if lean_info["has_solution"]:
                lean_badge = '<span class="badge badge-lean-verified">Lean 4 proof</span>'
            else:
                lean_badge = '<span class="badge badge-lean">Lean 4</span>'
        parts = [
            f'<div class="card-top"><h1>{html.escape(meta["title"])}</h1>'
            f'<div class="badges">{lean_badge}{badge(meta["status"])}</div></div>'
        ]
        posed_by, posed_year = meta.get("posed_by", ""), meta.get("posed_year", "")
        cat = meta.get("category", "")
        cat_label = CATEGORY_LABELS.get(cat, cat)
        prov_bits = []
        if posed_by or posed_year:
            prov_bits.append(f"Posed by {posed_by}" + (f", {posed_year}" if posed_year else ""))
        if cat_label:
            prov_bits.append(cat_label)
        if prov_bits:
            parts.append(f'<p class="provenance">{html.escape(" · ".join(prov_bits))}.</p>')

        parts.append(md_to_html(body))

        if lean_info:
            parts.append("<h2>Lean 4 Formalization</h2>")
            parts.append(
                f'<p class="muted">Module <code>{html.escape(lean_info["module"])}</code> '
                f'(<code>{html.escape(lean_info["file"])}</code>). '
                f'To certify a proof or disproof mechanically, add '
                f'<code>{html.escape(lean_info["solution_file"])}</code> defining '
                f'<code>proof : {html.escape(lean_info["module"])}.Statement</code> (or '
                f'<code>disproof : ¬ {html.escape(lean_info["module"])}.Statement</code>) and run '
                f'<code>python3 scripts/verify_proof.py --verify {html.escape(meta["id"])}</code>.</p>'
            )
            parts.append(f'<pre class="lean-code"><code>{html.escape(lean_info["code"])}</code></pre>')

        parts.append(f"<h2>Attempts ({len(attempts)})</h2>")
        if not attempts:
            parts.append(
                '<p class="muted">No attempts recorded yet. See AGENTS.md in the repository for the attempt protocol.</p>'
            )
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

    print(
        f"built site/ — {n_total} problems ({n_open} open/partial, {n_lean} Lean 4 formalized), "
        f"{sum(len(a) for _, _, a, _ in problems)} attempts"
    )


if __name__ == "__main__":
    main()
