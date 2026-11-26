# Repair from Lean errors vs. resampling (October–November 2026)

Fresh Mathlib theorems (added after the models' training data). Two arms with the **same number of Lean checks (4)**:
four independent attempts, or one attempt followed by up to three repair rounds in which the model sees Lean's error messages.

| Model | 4 independent attempts | 1 attempt + 3 repair rounds | Paired test |
|---|---|---|---|
| Claude Opus 5.5 (233 theorems) | 204 (87.6 %) | **229 (98.3 %)** | 26 : 1, p = 4·10⁻⁷ |
| GPT-6 Astra (187 theorems) | 47 (25 %) | **118 (63 %)** | 72 : 1, p = 8·10⁻²¹ |

Repair was also cheaper for Opus: $0.076 per theorem vs $0.225 (prompt caching, early stopping).

## Where the gain comes from (GPT-6 Astra, 191 theorems)

Success per round, converted to bits (log₂ of the gain factor, 95 % bootstrap CI):

- full Lean message vs. a blind "it failed" repair: **+1.8 bits** [1.4; 2.4], about ×3.5;
- only line numbers vs. blind: +0.1 bits [−0.3; 0.5], i.e. nothing usable;
- blind repair vs. a fresh attempt (the model avoids repeating its failed attempt): +0.85 bits [0.0; 1.7], about ×2.

## How much each model reads from the message

Gain factor Γ = (success per repair round) / (success of a fresh attempt after a failure), in bits per round:

| Model | Task set | Bits per round | 95 % CI of Γ |
|---|---|---|---|
| GPT-6 Astra | 191 fresh theorems | 2.7 | 4.4–11.0 |
| Claude Opus 5.5 | 233 fresh theorems | 1.4 | 1.9–3.8 |
| Claude Sonnet 5.5 | 100 of those | 1.4 | 1.8–4.6 |
| Claude Haiku 4.5 | 100 of those | 1.1 | 1.2–5.9 |
| Leanstral 1.5 (fixed repair loop) | 95 fresh theorems | 0.1 | 0.55–2.3 |

General-purpose models extract 1–3 bits per round, even the weak one (Haiku); the specialised prover Leanstral extracts
none (its interval includes zero gain), and earlier repair attempts with DeepSeek-Prover-V2-7B also gained nothing.
Reading feedback looks like a separate skill from proving ability. The sets differ, so cross-model comparisons are rough.
