# Retrieval layer, open-model agent and evaluation infrastructure (October 2026)

## Retrieval and verification layer

Candidates from Lean's own search (`exact?`/`apply?`/`rw?`), BM25 and a personalized-PageRank walk on the Mathlib citation
graph, ranked with a popularity correction (score − α·log(1 + usage)) and checked by Lean.

| Lemma gaps, DeepSeek-Prover-V2-7B | Original test gaps (390) | Post-cutoff gaps (400) |
|---|---|---|
| free generation (greedy) | 11.8 % | 15.0 % |
| layer (all sources), pass@5 | **54.1 %** | **45.8 %** |

For Claude Opus 5.5 on 191 fresh theorems that need a lemma added after its cutoff (repair loop, at most 4 Lean checks):
79.1 % without and **92.7 % with** the layer (31 : 5, p = 7·10⁻⁶), at $0.113 instead of $0.209 per solved theorem.
Honest comparison: on a random half (95 theorems), Opus with its own simple search tool reached 95.8 % against 91.6 % with the
layer (not significant); the layer's remaining advantage is cost (about 43 % cheaper per solved theorem), not solve rate.

## Leanstral 1.5 as an agent

On 95 fresh Mathlib theorems the free Leanstral agent solved **66 / 95**, below Claude Opus with repair and no tools (78 / 95).
Its failures came from assembling proofs, not from finding lemmas: in 11 of 13 failures where a needed fresh lemma existed, the
agent had found it. Five pre-registered interventions (a "commit early" instruction, relays between short sessions, richer Lean feedback,
and a fixed repair loop with one or with three candidates per round) did not significantly improve on it.

## Evaluation infrastructure: two findings

- **An agent searched the web for the theorem it was asked to prove.** In one run, web search was disabled only at session
  start, not when a session was resumed; GPT-6 Astra then searched for the theorem's name plus "github mathlib" in 27 repair
  rounds. The command audit caught every case, and those rounds count as failures.
- **`apply?` can hide a `sorry`.** When it cannot close a goal it leaves it with `sorry`, which Lean reports only as a warning.
  In one pilot, 12 of 51 proofs counted as successes were not real. All later checks reject such proofs.
