# What makes a theorem hard? Difficulty across models (November 2026)

Item-response analysis of first attempts on two sets where several models ran:
fresh Mathlib theorems (GPT-6 Astra, Claude Opus 5.5 and Mistral Leanstral 1.5 in several settings) and 233 fresh theorems with file context
(Claude Opus, Sonnet, Haiku). Model: logit P(setting s solves theorem i) = θ_s + β_s·(log proof length) + b_i + u (family) + w (setting),
with the exact marginal likelihood (Gauss–Hermite quadrature).

| Set | Share of difficulty explained by proof length | Of the rest: shared by all models | family-specific | setting-specific |
|---|---|---|---|---|
| Fresh Mathlib, 3 vendors | 0.28 | **0.68** | 0.18 | 0.14 |
| 233 fresh theorems, 3 Claude models | 0.22 | **0.81** | 0.19 (not separable) | – |

- The shared difficulty is large: its standard deviation is 2.6 (Mathlib) and 3.1 (Claude set) logit units.
- **Other models predict which theorems are hard** (5-fold cross-validation over theorems): AUC 0.80–0.84 with the difficulty
  estimated from other model families, against 0.60–0.71 from proof length alone.
- **A free model is a cheap probe:** Leanstral's outcomes raise the AUC for GPT-6 Astra (no context) from 0.54 to 0.81.
- **Reasoning effort shifts, it does not reorder:** for Astra at low, medium and high effort, the disattenuated correlation of
  per-theorem success rates is 0.95–1.05.
- **Weak models solve a subset of what strong models solve:** of the 16 theorems Haiku solved at least once, Opus solved all 16 in every attempt.
- **Difficulty is hard to see in the statement:** statement features explain R² ≈ 0.12 (three-vendor set) and ≈ 0 (Claude set).

Practical consequence: after a cheap model fails, the remaining theorems are harder for the strong model too
(Opus with search solves 34 % of the Leanstral agent's failures in one attempt vs. 82 % of the rest; with repair, 90 %), so an escalation chain needs repair, not a single
attempt of a stronger model. All of this is exploratory, computed after the runs.
