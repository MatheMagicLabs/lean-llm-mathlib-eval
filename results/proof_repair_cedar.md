# Automatic proof repair after real changes to AWS Cedar (November 2026)

When a codebase changes, existing proofs break and someone has to fix them. This experiment asks how many real breakages
in an industrial Lean codebase a model can repair on its own, at what cost, and how much the broken old proof helps.
Pre-registered (hypotheses hashed on 12 Nov 2026, before the main run); no deviations from the plan.

## Tasks

- **Source:** all 32 commits to `cedar-lean` in [cedar-spec](https://github.com/cedar-policy/cedar-spec) from 3 Jul to
  31 Oct 2026, i.e. after the release of Leanstral 1.5 and after the model's knowledge cutoff.
- **Candidates:** theorems whose name and statement are unchanged by a commit but whose proof was changed: 129 theorems.
- **Real breakages:** the old proof is put back into the new state of the tree and checked by Lean. 109 are rejected (with an
  error or a timeout); 20 still compile and are dropped.
- **Sets:** 3 pilot tasks excluded; main set **106 breakages from 13 commits**, including a Lean toolchain upgrade (v4.33.0)
  and content changes (new `has` formalisation, efficient set union, schema-based partial evaluation, …). A random 30 also
  run in an ablation arm.

## Setup

- The tree is checked out at the task's commit and built. The model sees the file up to `:= by` of the broken theorem and
  can use `lean_check`, declaration search, `grep` and file reading in that commit's source tree.
- **No leakage by construction:** the human repair of the target is never visible, and every other proof repaired in the same
  commit is hidden too (replaced by `sorry` in the file prefix, by a comment when read or grepped). A self-test checked this
  before the run.
- Model: Claude Opus 5.5 (effort medium) in the tool-using harness from [aws_cedar.md](aws_cedar.md), staged restarts,
  cap $2 per task. A proof counts only if Lean accepts it with no errors and no `sorry`, and it uses no `admit`,
  `native_decide` or search tactics.
- **Arms:**
  - *with old proof:* the prompt contains the commit title, changed files, the old proof and its Lean errors in the new state;
  - *without:* commit title and changed files only.

## Results

| Pre-registered hypothesis | Result | Verdict |
|---|---|---|
| H1: more than 80 % of the 106 breakages repaired | **104 / 106 (98.1 %)**, exact binomial p = 2·10⁻⁸, one-sided 95 % lower bound 94.2 % | confirmed |
| H2a: on the 30 ablation tasks, the old proof solves more | 29 / 30 with vs 29 / 30 without; the same task fails in both | not confirmed (ceiling) |
| H2b: on the same 30, the old proof makes repair cheaper | median $0.13 vs $0.26 per task, cheaper in 21 / 30, exact Wilcoxon p = 0.0065 | confirmed (Holm) |

- **Cost:** $23.52 for all 106 tasks, **$0.23 per repair** (median $0.12 per task, maximum $1.78). Median 31 s per task.
- **Effort:** 103 repairs in the first stage, 1 in the second; median 1 Lean check per task, and 59 of the 104 repairs passed
  the first Lean check.
- **Failures:** the 2 unrepaired breakages are correctness theorems of the optimised compiler after the switch to an
  efficient set union (commit 89f46dd1, 16 / 18 repaired); both hit the $2 cap.
- **What made a breakage hard:** neither the length of the human repair (over 100 lines: 16 / 16; up to 458 lines repaired)
  nor how much the human rewrote the proof (similarity old ~ human below 0.5: 15 / 15). The toolchain upgrade: 12 / 12;
  content changes: 92 / 94.

## What the old proof changes

Not *whether* the model repairs, but *how*:

| | with old proof | without |
|---|---|---|
| Solved (30 ablation tasks) | 29 | 29 |
| Median cost per task | $0.13 | $0.26 |
| Median Lean checks | 1 | 3 |
| Similarity of the repair to the human repair (median) | 0.87 | 0.15 |
| Similarity to the old proof (median) | 0.83 | 0.10 |

With the old proof, the model makes a small edit that usually passes on the first check and resembles the human commit, which
gives a reviewer a small diff. Without it, the model writes a completely new proof. No proof in the *without* arm resembles the
old proof (none ≥ 0.9), so there is no sign that the model reproduces old Cedar proofs from memory.

## Leakage check

54 repairs have similarity ≥ 0.9 to the human repair. In 46 of them the old proof was already nearly identical to the human
one, so a minimal edit lands on the same text. The other 8 (similarity to the human repair at least 0.1 higher than to the old
proof) were checked by hand, including every file the model read: all were built from visible material (the file prefix, the
old proof, definitions and newly added helper lemmas in other files), 7 of them on the first Lean check. No leak was found.

## Context and limitations

- Prior work: APE-Bench (tasks from mathlib's commit history) and CoqDEV / ADAPT (Coq projects, best result about 38 %).
  New here are an industrial Lean codebase, breakages after the model's cutoff, the cost per repair and the ablation arm. The
  task sets differ, so the rates are not directly comparable.
- One codebase, one model, one run per task. The breakages are real but come from four months of one project; the ablation
  arm is small (30) and at ceiling for success.
- Similarity is measured with `difflib` on proof text.
