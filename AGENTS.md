# The Attempt Protocol

This file is the working contract for anyone — human or AI agent — attempting a problem
in this repository. It is written so that an AI agent can be pointed at it plus one
problem file and produce a useful, honest attempt with no other instructions.

## One attempt = one file

Create `attempts/<problem-id>/YYYY-MM-DD-<attempter-slug>.md` from
`templates/ATTEMPT_TEMPLATE.md`. Never edit someone else's attempt file except to
update its `status` (see Verification below).

## Frontmatter

```yaml
---
problem: deletion-channel          # must match a problems/<id>.md
date: 2026-07-17
attempter: jane-doe                # person, or agent name
model: claude-fable-5              # AI attempts only; omit for humans
type: partial-result               # see vocabulary below
status: unverified
---
```

**`type` vocabulary** (pick the strongest honest label):

| type | meaning |
|---|---|
| `full-solution-claim` | You claim to resolve the problem. Extraordinary; expect scrutiny. |
| `partial-result` | A new theorem short of full resolution (special case, weaker hypothesis). |
| `new-bound` | A quantitative improvement on a known bound. |
| `reduction` | The problem is shown equivalent to / implied by another problem. |
| `numerical-evidence` | Computation supporting or undermining a conjecture. Include code. |
| `survey` | A synthesis of what's known that sharpens the problem. No new theorems. |
| `dead-end` | A documented failed approach and *why* it fails. Genuinely valuable. |

**`status`** starts at `unverified`. Later PRs may move it to `community-reviewed`,
`verified`, or `refuted`, with a note in the Verification section saying who checked
what.

## Rules of engagement

1. **Read everything first.** The problem file's "What is known" section and every
   earlier attempt in `attempts/<problem-id>/`. Do not rediscover a recorded dead end;
   if you extend or contradict an earlier attempt, cite it by filename.
2. **Label every claim.** Each numbered claim carries exactly one tag: `[proved]`
   (complete argument in this file or in a cited reference), `[sketch]` (you believe a
   full proof is routine and outline it), `[heuristic]` (plausible, not proof),
   `[conjectural]` (you believe it, no argument). Presenting a heuristic in the voice
   of a proof is the one unforgivable sin here.
3. **Novelty check.** Before claiming a result is new, say explicitly where you looked
   (which references, which searches) and why you believe it isn't already known.
4. **Show the failure, not just the success.** The Dead Ends section is mandatory when
   an approach was tried and abandoned. State the obstruction precisely.
5. **Numerical work is reproducible.** Code included in the file or linked in-repo,
   with exact parameters. State what the computation does and does not establish.
6. **Small and self-contained beats grand and gappy.** A fully proved lemma nudging a
   bound is worth more than a 10-page sketch of a full solution.

## For AI agents specifically

- State your model name and the date in the frontmatter. Do not claim access to
  literature you cannot cite specifically.
- If your training data may postdate a problem file's "What is known" section, a
  high-value move is a `survey` attempt updating it (with references) before trying
  to prove anything.
- Calibrate: an honest "`[heuristic]`, and here is the gap I could not close" attempt
  is a success, not a failure. The attempt log is a ratchet — it only works if every
  entry is trustworthy.
