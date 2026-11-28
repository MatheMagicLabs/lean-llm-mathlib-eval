# How LLMs prove (and fail to prove) new Mathlib theorems

Pre-registered experiments on large language models writing **Lean 4** proofs, using only theorems that were added
*after* the models' training data (contamination-controlled): Mathlib, and since November 2026 also industrial
verification code (AWS Cedar). Sections 1–3 come with full code and data; section 4 summarises later experiments.

Author: **Vincent Weinreich**. Experiments run September–November 2026.

> **Note on authorship.** The `.lean` proofs in `proofs/` were **written by an LLM** (Claude, configured model
> `claude-opus-5-5` and `Deepseek-4-Pro`) and checked by Lean. The experimental design, pre-registrations, task selection,
> verification pipeline and analysis are my work.

## Setup

- **Mathlib** at commit `d0a050ad6`, **Lean** `v4.35.0-rc2`.
- **Fresh theorems only:** every task comes from a theorem added to Mathlib after the model's knowledge cutoff.
- **Checking:** the model's proof replaces the human proof in the original Mathlib file, the file is cut after the
  theorem, and Lean checks it with Mathlib's own build options (`tools/stark_pruef.py`). A proof counts only with
  zero errors and no `sorry`. Before each run, the unmodified files are checked as a self-test.
- **Pre-registration:** hypotheses, tests and stopping rules were fixed (with SHA-256 hashes) before any result was seen.
  The original German documents are in `docs/de/`.

## 1. Long proofs (57 theorems, 25–142 human tactic steps)

The model writes the proof **without Lean access**; in round 2 it sees only Lean's error messages.

| | Round 1 | Up to round 2 |
|---|---|---|
| unaided | 31 / 57 (54 %) | 41 / 57 (72 %) |
| with an outline of the human proof | 27 / 57 (47 %) | 42 / 57 (74 %) |

- Success drops with proof length (Cochran–Armitage, p = 0.039), mainly for proofs of **50+ steps (3 of 9)**.
- An outline of the human proof does **not** help.
- The most common identified causes of failure are **unknown names (20)** and **type/instance errors (19)**.
- No successful proof uses search tactics (`exact?`, `apply?`). Median similarity to the human proof: 0.15.

**44 of the 57 theorems** have a verified model proof in `proofs/long/`.

## 2. Short proofs and a strategy hint (80 theorems, 3–25 steps)

- Unaided: 73 / 80 in round 1, **79 / 80** within three rounds. With a hint on the human proof strategy: 68 / 80 → 78 / 80.
- The hint does not help. Verified proofs: `proofs/short/` (79 files).

## 3. Lemma gaps: which lemma does a prover pick? (1,000 gaps)

In 1,000 proofs from new Mathlib theorems, one explicitly named lemma was removed and **DeepSeek-Prover-V2-7B**
(4-bit, run locally with MLX) had to fill the gap.

- **Same lemma as the human:** 11.9 %. **Invented, non-existent name:** 21.1 %.
- Where it chose a different existing lemma, it was on average **3.2× more widely used** in Mathlib than the
  human's choice (permutation test, p < 0.0001); the effect sits almost entirely where the human used a rare, specific lemma.
- **Stage 2 (Lean check of all 305 substitutes):** only **15 (4.9 %)** type-check, and almost none where the human lemma
  was actually needed. The popular substitutes are errors, not alternative proofs: the bottleneck is *finding* the specific lemma.

Code and raw outputs: `lemma_gaps/`.

## 4. Later experiments (October–November 2026)

Summaries in `results/` (English). Each experiment was pre-registered with hashed hypotheses before any result was seen;
exploratory analyses are marked as such.

- **AWS Cedar, industrial verification code** ([results/aws_cedar.md](results/aws_cedar.md)). The free model Leanstral 1.5
  as an agent proves 139 of 195 recently added Cedar theorems; Claude Opus 5.5 in a tool-using Lean harness proves all 56 that
  remain, so the chain solves **195 / 195 for $12.67** of API cost (about 6.5 ¢ per theorem).
- **Automatic repair of real Cedar breakages** ([results/proof_repair_cedar.md](results/proof_repair_cedar.md)). Of 106
  proofs broken by real cedar-spec commits after the model's cutoff, Claude Opus 5.5 repairs **104 (98 %) for $0.23 per
  repair**, with sibling repairs from the same commit hidden. Showing the broken old proof does not change the success rate
  but halves the median cost and turns rewrites into small diffs close to the human commit.
- **Repair from Lean errors beats resampling** ([results/repair_from_lean_errors.md](results/repair_from_lean_errors.md)).
  At an equal budget of 4 Lean checks: Opus 229 vs 204 of 233 fresh theorems, GPT-6 Astra 118 vs 47 of 187. General-purpose
  models extract 1–3 bits per round from Lean's messages; the specialised prover Leanstral extracts none.
- **What makes a theorem hard** ([results/difficulty_across_models.md](results/difficulty_across_models.md)). 68–81 % of
  difficulty beyond proof length is shared across models from three vendors; a free model's failures predict which theorems
  are hard for frontier models (AUC 0.54 → 0.81); more reasoning effort shifts success rates without reordering theorems.
- **Retrieval layer, open-model agent, evaluation infrastructure** ([results/retrieval_and_agents.md](results/retrieval_and_agents.md)).
  Lean-checked retrieval raises lemma-gap filling from 12 % to 54 % (46 % post-cutoff) for DeepSeek-Prover-V2-7B and lifts
  Opus from 79 % to 93 % on theorems needing a new lemma; command audits caught an agent searching the web for its theorem.

Related public repositories: [lean-formal-results](https://github.com/MatheMagicLabs/lean-formal-results) (Lean-checked
disproofs of two formal-conjectures statements, lemma-layer data) and
[rubiks-cube-lean](https://github.com/MatheMagicLabs/rubiks-cube-lean) (Rubik's cube group, 20 ≤ God's number ≤ 28).

## Repository layout

```
proofs/long/     44 verified LLM proofs of long new Mathlib theorems (statement + proof, with metadata header)
proofs/short/    79 verified LLM proofs of short new Mathlib theorems
data/            tasks, every attempt (incl. failed ones) and every Lean check result
lemma_gaps/      lemma-gap experiment: run script, model outputs, Lean stage-2 check
tools/           Lean checker (stark_pruef.py), Lean metaprograms used for extraction (Extract.lean, Deprec.lean)
docs/de/         original pre-registrations and result reports (German)
results/         English summaries of the October–November 2026 experiments (section 4)
```

## Reproducing a check

```bash
git clone https://github.com/leanprover-community/mathlib4 && cd mathlib4
git checkout d0a050ad6 && lake exe cache get
python tools/stark_pruef.py --mathlib <path-to-mathlib4> --patches data/long/tasks.jsonl \
  --beweise data/long/all_attempts.jsonl --out checks.jsonl --workers 4 --timeout 600
```

## Limitations

One model family per experiment; the lemma-gap prover is a quantised 7B model; contamination checks found no evidence of
leakage but cannot rule it out. Some scripts and reports are in German. For section 4, this repository so far contains
summaries only; scripts and raw outputs of those experiments are not included yet.

## License

Apache 2.0 (as Mathlib). Theorem statements are taken from Mathlib (Apache 2.0, © the Mathlib contributors).
