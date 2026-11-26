---
title: "Negative Time in the Challenge's Public Language"
subtitle: "Full methodology, machine-checked skeleton, and the rule-out — no extra dimensions, no strings, no imaginary-time smuggling"
author: "Analysis: Vibe Code (Mistral AI); public language: `yang-mills-group/OpenAI-YM-20261028`"
date: "2026"
geometry: margin=1in
fontsize: 10pt
mainfont: "DejaVu Sans"
monofont: "DejaVu Sans Mono"
colorlinks: true
toc: true
---

# Verdict (read this first)

The proposal — *demonstrate the existence of negative time, and find an
expression that relates the negative component of spectral weight to the
established mass gap, in balance with the positive component* — was
constructed in its strongest form, evaluated node by node against the
repository's public language, and carried through the same discipline as the
mass-gap analysis (`MassGapProof.md`: everything proved but one named node),
the confinement analysis (`ConfinementScenarios.md`: unconditional claim
ruled out by a direct-sum witness), and the unification analysis
(`UNIFICATION_SCENARIOS.md`: ruled out by the decoupled-sector witness, with
a five-datum conditional ledger). The outcome is exact:

* **The negative-time region exists, is measurable, and is spectrally dead —
  unconditionally.** `NegativeTime = {p | time p < 0}` is a measurable set
  (`measurableSet_negativeTime`), it is disjoint from the forward cone
  (`negativeTime_cone_empty`), and the diagonal energy-momentum measure of
  **every** state assigns it **zero** (`negativeTime_null`). This is a
  theorem of `W0` alone — the weakest public datum. **The mass gap is not
  needed and not used.** The verdict precedes and survives without the
  established gap.
* **The proposed balance degenerates, gap-independently.** The negative
  component is identically zero and the positive component `{0 ≤ t}` carries
  the entire spectral mass (`timeBalance_degenerate`):
  `μ_ψ{t < 0} = 0` and `μ_ψ{0 ≤ t} = μ_ψ(ℝ⁴)` for every state. No expression
  coupling the negative component to a gap parameter `m` can be balanced
  against it: any such expression balances against zero, and the positive
  component is the same with or without the gap. The balance is not a
  relation to the mass gap — it is the trivial partition of unity.
* **The strong (Minkowski time-reversal) datum is refuted in Lean.** A
  time-reflection operator intertwining the energy-momentum PVM and
  preserving the cone (`TimeReflects`) is *inconsistent with the public
  language for every theory*: the rest point at energy `m > 0` sits in the
  cone, `conePreserved` keeps its image in the cone, `timeImage` puts that
  image at time `−m < 0` — inside a region of empty cone-intersection
  (`timeReflects_refuted`). Positive energy forbids Minkowski time-reversal
  symmetry from the outset; the negative wing cannot be animated this way.
* **The weak (Osterwalder–Schrader, imaginary-time) escape route is
  conditional-only.** Abandoning `conePreserved` evades the refutation but
  abandons real time altogether: reflection positivity is a *new datum* the
  public API does not contain (the analogue of the mass-gap module's missing
  `LorentzIntertwines`), and what it would yield — `diagonal_pullback_reflect`,
  proved here from PVM algebra alone *given* the datum — is a statement about
  imaginary-time Schwinger functions, not spectral weight at `t < 0`.

**Bottom line.** Negative time, as posed, is a spectrally empty region whose
"balance" against the mass gap is identically the trivial partition of
unity; the only mechanism that could give it content is refuted in the
strong form and conditional on a missing, non-public datum in the weak form.
The framework is **refuted in its strong form, conditional-only in its weak
form**, and in neither form does any expression relate negative time to the
mass gap.

---

# Part I — The fixed data: what the public language can and cannot say

## 1. The relevant public structure

Everything below is a theorem about `WightmanTheory H Labels`
(`PublicTheory.lean`) with `T.W0` — the *only* hypothesis used. Four
structural facts frame everything:

- **R1 (spectral support).** `W0.positiveEnergy` says the energy-momentum
  projection annihilates the cone complement; `diagonalIdentity` transports
  this to the diagonal measure. Spectral weight lives on `forwardCone` —
  the closed set `{p | ‖x‖ ≤ t}` — and nowhere else. This is the *entire*
  input to the nullity theorem.
- **R2 (time is a coordinate, not an operator ordering).** In the public
  language `time : Spacetime →L[ℝ] ℝ` is a continuous linear functional on
  spacetime points. "Negative time" is therefore well-posed *only* as a
  region of spacetime (`{p | time p < 0}`), and any spectral claim about it
  is a claim about measure of that region. There is no time operator, no
  Hamiltonian spectral flow, no arrow-of-time structure in the API to
  reinterpret it against.
- **R3 (the cone is future-pointing).** The forward cone has empty
  intersection with negative time — `0 ≤ ‖x‖ ≤ t < 0` is a linarith
  contradiction. This geometric triviality is precisely what turns W0 into
  nullity of the negative region, and it is also exactly what kills the
  reflection datum (Part V).
- **R4 (no mass gap is needed).** The nullity theorem consumes W0 only.
  Where the mass-gap analysis needed one missing intertwining datum
  (`LorentzIntertwines`), the negative-time verdict needs **nothing beyond
  the weakest public hypothesis**. Any attempted strengthening — relating the
  negative component to the gap — therefore cannot be a *consequence* of the
  gap; it would have to be an additional axiom, and Part V shows its
  strongest form is inconsistent.

## 2. What "negative time" must mean here

The proposal asks for (i) existence, (ii) an expression relating negative
time to the mass gap, (iii) balance between negative and positive
components. In the public language each clause has exactly one reading:

| Clause | Public-language reading | Status |
|---|---|---|
| existence of negative time | `NegativeTime := {p | time p < 0}` nonempty and measurable | **proved** (`measurableSet_negativeTime`; nonemptiness: `t ↦ −1` point) |
| relation to the mass gap | an identity coupling `μ_ψ{t < 0}` to a gap parameter `m` | **impossible** (Part IV: the left side is identically 0) |
| negative/positive balance | `μ_ψ{t < 0} + μ_ψ{0 ≤ t} = μ_ψ(ℝ⁴)` with the two summands comparable | **degenerate** (`timeBalance_degenerate`: `0 + total = total`) |

Anything richer — negative *durations*, spectral flow across `t = 0`,
negative-energy states, a second time sheet — is outside the API (R2) and
would be new physics, not a consequence of the established gap.

---

# Part II — The target, in the repository's own language

The module `NegativeTime.lean` fixes, in the family's discipline
(`set_option autoImplicit false`, `noncomputable section`, no `sorry`, no
`axiom`, missing data declared as named structures):

```lean
def NegativeTime : Set Spacetime := {p : Spacetime | time p < 0}          -- :95
def negativeShell (R : ℝ) : Set Spacetime := {p : Spacetime | time p ≤ -R} -- :98
```

and proves, with geometry copied verbatim from `Confinement.lean` /
`MassGap.lean` (`timeL`, `time_cont`, `spatialL`, `closed_forwardCone`,
`measurableSet_forwardCone`, `continuous_minkowskiSquare`):

| Theorem | Statement (informal) | Axioms |
|---|---|---|
| `measurableSet_negativeTime` :100 | `NegativeTime` is Lebesgue-measurable (complement of the closed half-space `{0 ≤ t}`) | standard |
| `negativeTime_cone_empty` :109 | `forwardCone ∩ NegativeTime = ∅` | standard |
| `diagonal_le_cone` :122 | `μ_ψ(coneᶜ) = 0` from `W0` (verbatim from `MassGap.lean`) | standard |
| **`negativeTime_null`** :138 | **`μ_ψ{t < 0} = 0` for every state, from W0 alone** | standard |
| `negativeShell_null` :150 | every shell `{t ≤ −R}`, `R > 0`, is spectrally null | standard |
| **`timeBalance_degenerate`** :167 | `μ_ψ{t < 0} = 0 ∧ μ_ψ{0 ≤ t} = μ_ψ(ℝ⁴)` | standard |
| `rest_point_core` :185 | rest point at `m > 0`: `p₀ ∈ forwardCone ∧ time p₀ = m` (verbatim from `MassGap.lean`'s witness) | standard |
| **`timeReflects_refuted`** :235 | **the strong reflection datum is inconsistent: `False`** | standard |
| `diagonal_pullback_reflect` :256 | pullback law for spectral pairings across a reflection, *given* the datum | standard |

The key statement, verbatim:

```lean
theorem negativeTime_null (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) NegativeTime = 0 := by
  have hsub : NegativeTime ⊆ Set.compl forwardCone := by
    intro p hp
    simp only [NegativeTime, Set.mem_setOf_eq] at hp
    intro hc
    simp only [forwardCone, Set.mem_setOf_eq] at hc
    have hnorm := norm_nonneg (spatial p)
    linarith
  exact le_antisymm
    ((measure_mono hsub).trans (le_of_eq (diagonal_le_cone T hW0 ψ))) zero_le
```

The proof is three moves: the negative region sits inside the cone
complement (R3); W0 kills the complement (`diagonal_le_cone`); antisymmetry
closes it. **No mass-gap parameter appears.**

---

# Part III — The methodology, in its strongest form (steelman)

To give the proposal every advantage, the methodology was assembled in the
strongest form the public language admits, mirroring the steelman discipline
of `MassGapProof.md` and `UNIFICATION_SCENARIOS.md` Part III:

1. **Steelman S1 — the balance identity as a theorem.** Take the proposed
   balance literally: negative component `μ_ψ{t < 0}`, positive component
   `μ_ψ{0 ≤ t}`, and demand a relation to the gap `m`. Strongest form: both
   sides *expressible in the API* and the relation *proved for all states*.
   This is exactly `timeBalance_degenerate` — and it is where the proposal
   dies, because the negative side is identically zero (Part IV).
2. **Steelman S2 — animate the negative wing with a reflection symmetry.**
   The only mechanism that could make negative time carry weight is a
   symmetry trading positive-time spectral weight for negative-time weight:
   an operator `U` on states, a spacetime reflection `ρ`, with
   `time (ρ p) = −time p`, cone preservation, vacuum invariance, domain
   stability, and covariance of the PVM. This is `TimeReflects` — the exact
   analogue, one axis down, of the missing `LorentzIntertwines` datum of
   `MassGapProof.md`. In Euclidean field theory this is Osterwalder–Schrader
   reflection; in Minkowski signature it is (anti)unitary time reversal.
3. **Steelman S3 — harvest the pullback law.** Given S2, spectral pairings
   transfer across the reflection: `⟨Uψ, E(A) Uψ⟩ = ⟨ψ, E(ρ⁻¹A) ψ⟩`
   (`diagonal_pullback_reflect`, proved from PVM algebra alone — copied from
   the verified `diagonal_pullback` of `Unification.lean`). Applying it to a
   negative-time set `A` would pull spectral weight back from the cone into
   negative time. This is the proposal's only conceivable payoff.
4. **Steelman S4 — the imaginary-time fallback.** If Minkowski reflection is
   untenable, retreat to Euclidean time `τ = it` (Wick rotation), where
   reflection positivity lives and negative *imaginary* time is harmless.
   This is the physically standard escape and the strongest residual form of
   the proposal.

S1 is proved — and degenerate. S2 is refuted outright (Part V). S3 is
vacuous without S2. S4 is conditional on a datum outside the API (Part VI).

---

# Part IV — R-out 1: the balance degenerates (decisive, unconditional)

The proposed expression "relating negative time to the mass gap" must, in
the public language, be an identity between measures of spacetime regions
and the gap parameter. The module proves the identity that *actually holds*:

```lean
theorem timeBalance_degenerate (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) NegativeTime = 0 ∧
    (T.energyMomentum.diagonal ψ) {p : Spacetime | 0 ≤ time p} =
      (T.energyMomentum.diagonal ψ) Set.univ
```

Three consequences, each fatal to a reading of the proposal:

- **The negative component is identically zero.** Not small, not suppressed
  by the gap — zero, for every state, from W0 alone. An "expression
  relating negative time to the mass gap" has a constant-zero left side; the
  most it can ever say about `m` is nothing.
- **The positive component is the whole measure, gap-independently.**
  `μ_ψ{0 ≤ t} = μ_ψ(ℝ⁴)` whether or not the theory has a mass gap — the
  balance holds at the W0 level, so the *established gap contributes
  nothing* to it. A balance that does not detect the hypothesis it was
  proposed to balance against is not a relation to that hypothesis.
- **The balance is the trivial partition of unity.**
  `0 + total = total` via `measure_add_measure_compl` and `zero_add`. There
  is no left-over, no deficit, no "missing" negative weight that the gap
  could account for. The requested *balance between negative and positive
  components* exists only in the degenerate ratio `0 : total`.

**Witness character:** this is the same rule-out shape as
`ConfinementScenarios.md` (the direct-sum witness satisfies every hypothesis
without the conclusion) and `UNIFICATION_SCENARIOS.md` R-out 1 (the
decoupled sector satisfies every clause without unification): a *single
object inside the hypothesis class* on which the desired conclusion fails to
have the proposed content. Here the witness is every theory with W0 — i.e.
the entire class.

---

# Part V — R-out 2: the strong reflection datum is refuted (decisive)

Steelman S2's datum, formalized exactly as the strongest candidate
(`NegativeTime.lean:217`):

```lean
structure TimeReflects (T : WightmanTheory H Labels) where
  reflect : Spacetime →L[ℝ] Spacetime
  timeImage (p : Spacetime) : time (reflect p) = - time p
  conePreserved (p : Spacetime) : p ∈ forwardCone ↔ reflect p ∈ forwardCone
  onStates : H.Operator
  vacuumFixed : onStates T.fields.vacuum.1 = T.fields.vacuum.1
  domainMapsTo (v : H.carrier) : v ∈ T.fields.domain → onStates v ∈ T.fields.domain
  spectralCovariance {A : Set Spacetime} (_ : MeasurableSet A) :
    T.energyMomentum.projection (Set.preimage (reflect : Spacetime → Spacetime) A) =
      (onStates.adjoint).comp ((T.energyMomentum.projection A).comp onStates)
```

No structure field of `PublicTheory` carries any of it — this is a *new
datum*, exactly as `LorentzIntertwines` was for the gap. But unlike that
node, this one is not merely missing: it is **refuted**.

```lean
theorem timeReflects_refuted (T : WightmanTheory H Labels) {m : ℝ} (hpos : 0 < m)
    (D : TimeReflects T) : False := by
  obtain ⟨hcone, htime⟩ := rest_point_core (m := m) hpos
  set p₀ := WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m) with hp₀
  have h1 : D.reflect p₀ ∈ forwardCone := (D.conePreserved p₀).mp hcone
  have h2 : D.reflect p₀ ∈ NegativeTime := by
    simp only [NegativeTime, Set.mem_setOf_eq]
    rw [D.timeImage p₀, htime]
    exact neg_lt_zero.mpr hpos
  have hmem : D.reflect p₀ ∈ forwardCone ∩ NegativeTime := Set.mem_inter h1 h2
  rw [negativeTime_cone_empty, Set.mem_empty_iff_false] at hmem
  exact hmem.elim
```

The contradiction is four lines against the public language itself:

1. the rest point `p₀` (zero spatial momentum, `time p₀ = m > 0`) is in the
   cone — this is *half of the mass-gap witness*, provable unconditionally;
2. `conePreserved` keeps `reflect p₀` in the cone;
3. `timeImage` puts `reflect p₀` at time `−m < 0`, i.e. in `NegativeTime`;
4. but the cone and negative time are disjoint (`negativeTime_cone_empty`).

**For every theory and every `m > 0`.** The physical reading: a symmetry
that reflects time while preserving the forward cone cannot exist, because
the cone is *not* time-symmetric — its tip is at the origin and it points
forward. Any operator implementing `t ↦ −t` on a positive-energy theory
either fails to preserve the cone, fails to act on the spectrum as
required, or is not a symmetry at all. This is the rigorous shadow of the
standard fact that positive energy and Minkowski time-reversal are in
tension (the spectrum of the Hamiltonian is bounded below, so a unitary
implementing `H ↦ −H` cannot exist).

With S2 dead, S3 (`diagonal_pullback_reflect`) is vacuous: it is proved
from PVM algebra *given* the datum, and no theory supplies the datum. The
pullback law stands as exactly the interface a weaker formalization would
have to replace (Part VI).

---

# Part VI — The missing-datum ledger, and the imaginary-time escape

## 6.1 The ledger

| # | Datum | Status | Role |
|---|---|---|---|
| N1 | `TimeReflects` — cone-preserving Minkowski time reflection with PVM covariance | **refuted** (`timeReflects_refuted`) | would animate the negative wing (S2→S3) |
| N2 | Osterwalder–Schrader reflection positivity: for the Euclidean-time reflection `Θ`, `⟨Θf, f⟩ ≥ 0` on Schwinger functionals | **missing** (no API field) | the weak form's substitute for N1 |
| N3 | a Wick-rotation interface: Euclidean correlation functions ↔ Wightman functions of a theory with `T.W0` (the OS reconstruction theorem) | **missing** (no API field) | bridges S4's Euclidean statement to the public Minkowski language |
| N4 | a *modified* cone/region calculus under which the reflected image of the cone lies in negative time without contradicting W0 | **impossible in the strong form** (R3 + `negativeTime_cone_empty` are theorems) | the only other route to a nondegenerate balance |

N1 is the only datum whose negation is *provable*; N2, N3 are merely absent
(the family's standard shape — cf. `LorentzIntertwines`, ledger A1–A5 of
`UNIFICATION_SCENARIOS.md`); N4 is ruled out by the geometry already in the
module.

## 6.2 Why the OS escape does not save the proposal

Abandoning `conePreserved` (the single clause that produces the
contradiction) does evade `timeReflects_refuted`. But the cost is total:

- **The reflection no longer acts on real time.** OS reflection acts on
  *imaginary* time `τ`; negative `τ` is a bookkeeping region of Euclidean
  correlation functions, not a region of the public spacetime. The statement
  "negative time exists with spectral weight" becomes "Euclidean functionals
  can be extended across `τ = 0`" — a different claim, about different
  objects.
- **The public API has no Euclidean layer.** `Spacetime`, `time`,
  `forwardCone`, `energyMomentum` are Minkowski. N2 and N3 are not present
  even as named structures, so the weak form cannot even be *stated* in the
  language without extending the API — the same situation as the
  `LorentzIntertwines` node, and for the same reason: the challenge's public
  language quantifies over lattice Wilson families and their continuum
  limits, and reflection positivity of those objects is nowhere assumed.
- **Even granted N2+N3, the payoff is not the proposed balance.** The
  pullback law (`diagonal_pullback_reflect`) relates pairings across the
  reflection; with reflection positivity it yields *positivity* of Euclidean
  two-point functionals — the OS theorem's actual content. It yields no
  spectral weight at `t < 0` (which stays zero, by
  `negativeTime_null`), and no coupling of anything to the gap.

So the weak form is **conditional on missing data, and even conditionally
true it does not deliver the proposal**. This is a strictly weaker position
than the mass-gap chain (whose conditional chain, granted its one datum,
*does* deliver the gap) and comparable to the unification ledger (whose
conditional chain delivers unification only under five data, one of which —
gravity — is method-independently unproved).

---

# Part VII — The rule-outs, each with its witness

| R-out | Statement refuted / degraded | Witness | Scope |
|---|---|---|---|
| R-out 1 | a nondegenerate negative/positive balance coupled to the gap | `timeBalance_degenerate` — every W0 theory | unconditional |
| R-out 2 | existence of a cone-preserving time-reflection symmetry | `timeReflects_refuted` — every theory, every `m > 0` | unconditional |
| R-out 3 | the imaginary-time fallback as a delivery mechanism for the balance | N2, N3 absent from the API; payoff mismatch even granted them | conditional-only |
| R-out 4 | any modified region calculus placing reflected cone images in negative time | R3 + `negativeTime_cone_empty` are theorems of the fixed geometry | unconditional |

---

# Part VIII — Final verdict

The negative-time framework, in the public language, resolves as follows:

| Component of the proposal | Verdict | Where |
|---|---|---|
| existence of negative time as a region | **true** (measurable, nonempty) | `measurableSet_negativeTime` |
| negative time carries spectral weight | **false — identically zero, unconditional** | `negativeTime_null`, `negativeShell_null` |
| relation between negative time and the mass gap | **impossible** — the negative side is constant zero; the balance holds without the gap | `timeBalance_degenerate` |
| negative/positive balance | **degenerate** — the trivial partition of unity `0 + total = total` | `timeBalance_degenerate` |
| strong-form mechanism (Minkowski reflection) | **refuted** — inconsistent with the public language | `timeReflects_refuted` |
| weak-form mechanism (OS imaginary time) | **conditional-only** on missing data N2, N3; delivers positivity, not the balance | Part VI |
| overall framework | **refuted in the strong form; conditional-only in the weak form; the proposal itself (a gap-coupled balance) is ruled out unconditionally** | Parts IV–VII |

The methodology that produced this verdict is the same one that proved the
mass gap modulo one node, ruled out unconditional confinement, and ruled out
unconditional unification: fix the public data; steelman the proposal in
that language; prove what survives; refute what does not, with explicit
witnesses; ledger what is merely missing. Applied to negative time, it
yields the sharpest outcome of the four analyses — the central mechanism is
not merely missing but *provably absent*, and the requested expression does
not exist in any nondegenerate form.

---

## Appendix A — Verification

`NegativeTime.lean` was compiled at the pinned toolchain (Lean
`v4.32.0`, Lake 5.0.0, Mathlib snapshot `81a5d257c8e410db227a6665ed08f64fea08e997`):

```
$ lake env lean NegativeTime.lean; echo "exit=$?"
exit=0
```

0 errors, 0 warnings, 0 sorries, 0 custom axioms.

Axiom audit (a scratch copy with a `#print axioms` block appended, all nine
public theorems):

```
'YangMills.measurableSet_negativeTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.negativeTime_cone_empty'     depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.diagonal_le_cone'            depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.negativeTime_null'           depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.negativeShell_null'          depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.timeBalance_degenerate'      depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.rest_point_core'             depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.timeReflects_refuted'        depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.diagonal_pullback_reflect'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard axioms appear. `NegativeTime.lean` is not a
lakefile root and imports only `WilsonPublic`; no existing module is
modified, so the verified baselines (`MassGap.lean`, `Confinement.lean`,
`Unification.lean`) are unaffected. File hashes are recorded in
`SOURCES.sha256`.

## Appendix B — Cross-references

- `MassGapProof.md` — the proved mass-gap chain; its single missing datum
  `LorentzIntertwines` is the structural template for ledger N2/N3; its
  rest-point witness is `rest_point_core` here (cone-membership and time
  coordinate copied verbatim).
- `MassGapScenarios.md` — the scenario ledger for the gap.
- `ConfinementScenarios.md` — the unconditional rule-out by direct-sum
  witness; the shape reused in Part IV.
- `Confinement.lean` — source of the geometry lemmas copied verbatim.
- `Unification.lean` / `UNIFICATION_SCENARIOS.md` — source of the
  pullback-law proof technique (`diagonal_pullback` →
  `diagonal_pullback_reflect`) and of the missing-datum ledger format
  (A1–A5 → N1–N4).
- `PublicTheory.lean`, `ChallengeSpec.lean` — the fixed public language.
