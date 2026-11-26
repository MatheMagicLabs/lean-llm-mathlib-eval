# Beyond Mathlib: proving new theorems in AWS Cedar (November 2026)

[Cedar](https://github.com/cedar-policy/cedar-spec) is AWS's authorization-policy language; its specification and
correctness proofs are written in Lean 4. This is real industrial verification code, not textbook mathematics.

## Tasks

- cedar-spec at commit `1231010f` (30 Oct 2026), Lean v4.35.0.
- **Fresh theorems only:** theorems in `cedar-lean/Cedar/Thm` whose names did not exist on 25 June 2026 (the last commit
  before Mistral's Leanstral 1.5 was released on 2 July 2026), with tactic proofs and without `sorry`/`native_decide`.
- Two random samples: V1 (95 theorems) and V1b (100 further theorems, disjoint from V1). Every task passed a self-test first
  (the task with `sorry` compiles; the human proof is accepted).
- The model sees the file up to `:= by` and the source tree of that commit, never the human proof. A proof counts only if
  Lean accepts it with no errors and no `sorry`, it uses no forbidden tactic, and the command log shows no access outside
  the sandbox.

## Results

**Step 1 – Leanstral 1.5 as an agent (free model, Mistral Vibe, 600 s and 60 tool calls per theorem):**

| Sample | Solved |
|---|---|
| V1 | 70 / 95 (74 %, 95 % CI 64–81 %) |
| V1b | 69 / 100 |
| together | 139 / 195 (71 %) |

By length of the human proof (V1): 1–3 lines 17/17, 4–9 lines 35/39, 10–29 lines 16/29, 30+ lines 2/10.

**Step 2 – Claude Opus 5.5 with a tool-using Lean harness on the 56 theorems Leanstral did not solve.**
The harness gives Opus `lean_check`, declaration search, `grep` and file reading in the Cedar tree, with staged restarts and
a cap of $2 per theorem.

| | Harness | Plain agent loop |
|---|---|---|
| Solved (of 56) | **56 / 56** | 48 / 56 |
| API cost | **$12.67** ($0.23 per solved theorem) | $21.95 ($0.46) |

Pre-registered test (harness > loop, exact one-sided McNemar): 8 : 0, p = 0.004. **Caveat:** 6 of the loop's 8 failures came
from searching until the call limit without ever submitting a proof (the loop arm had no search cap). The harness's main
advantage is that it checks drafts with Lean early; a loop with a search cap would probably have done better.

**Escalation chain (free model first, Opus only on the rest):**

| Sample | Leanstral | + Opus harness |
|---|---|---|
| V1 (95) | 70 | **95 / 95** |
| V1b (100) | 69 | **100 / 100** |
| together (195) | 139 | **195 / 195** for $12.67 of Opus cost, about 6.5 ¢ per theorem |

## Checks

- No human proof appeared in any source the agent could see. Highly similar solutions (similarity ≥ 0.9 to the human proof)
  all have a near-identical sibling proof earlier in the same file, which the agent read and adapted, as the Cedar authors did.
- Leanstral's length dependence replicates across the two samples: a per-line success factor of 0.972 (V1) and 0.971 (V1b);
  the V1 fit predicted 70.1 solved theorems in V1b, and 69 were solved.

## Limitations

One run per theorem; Leanstral's training cutoff is unknown (its release date is an upper bound), and Opus's exact cutoff
relative to these theorems was not verified. The sample reflects what new Cedar theorems look like: many short helper lemmas.
Long main theorems (linker, type checker, SymCC compiler) are the hard part for the free model.
