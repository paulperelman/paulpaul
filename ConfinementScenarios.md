# Confinement in the challenge's public language: simultaneous evaluation and rule-out

**Companion repository:** `yang-mills-group/OpenAI-YM-20261028`
**Machine-checked companion:** `Confinement.lean` (this branch) — compiles with **0 errors, 0 warnings, 0 `sorry`, 0 `axiom`**; every theorem depends on `[propext, Classical.choice, Quot.sound]` only.
**Predecessor:** `MassGapScenarios.md` (mass gap), `MassGapProof.md` (Lean walkthrough).

---

## Verdict (read this first)

The repository's confinement methodology — the Wilson-lattice → Wightman reconstruction pipeline summarized by `JointExistence` with its `nonfree : TraceTest` clause — **cannot establish that quarks are confined**, i.e. that "fundamental theoretical particles (quarks) cannot exist freely and are always confined within color-bound quantum states."

The failure is structural, not a matter of missing estimates:

1. **Sector invisibility.** Every hypothesis in `WilsonRegularity`, `Hierarchy`, `Reconstructed`, `OperatorProductExpansion`, and `TraceTest` is a vacuum correlation of **gauge-invariant** insertions. A free colored sector `K` adjoined to the physical theory (`H ⊕ K`, vacuum `Ω ⊕ 0`) changes **none** of these hypotheses — the original block is untouched — yet it makes freeness maximally false. No evaluation of the stated methodology can distinguish the confined theory from this deviation.

2. **The gauge group is an orphan in `PublicTheory.lean`.** `GaugeGroup`/`IsSimple` exist, but no structure field of `WightmanTheory`, `FieldSystem`, `PoincareAction`, or `EnergyMomentumMeasure` references them. There is no Gauss law in the public Wightman language, hence no mechanism that could ever force charged carriers off the mass shell. `Confinement.lean` proves the exact conditional statement that would close this gap (`freeLabel_gauge_trivial`, `confined_of_colorCharged`) and exhibits precisely which datum is missing (`ShellNeutral`); that datum is not derivable from any public clause.

3. **What the mass gap does exclude is narrow and proved.** `free_label_mass_ge_of_massGap` shows: under the challenge's gap condition, a spectrally free label must have all its on-shell vacuum excitations at masses `≥ m`. The gap excludes only *light* free carriers; a free, colored, massive sector (mass `≥ m`) survives every public hypothesis. The mass-gap route to confinement is therefore quantitatively too weak, not just structurally blind.

**Conclusion: rule out.** The methodology, as specified, cannot reach confinement; only an extension of the public language (a Gauss-law / gauge-intertwining interface between `WightmanTheory` and `GaugeGroup`, with shell-neutrality of on-shell excitations) could.

---

## Part I — The methodology under evaluation: complete inventory

The confinement-relevant apparatus of the challenge lives in three layers. Exact line references from this branch:

### Layer 1 — pure gauge side (`PublicTheory.lean`)

| Object | Role | Confinement-relevant? |
|---|---|---|
| `GaugeGroup` (with `.image`, `IsSimple`) | compact simple gauge group | **Orphan** — referenced by nothing in `WightmanTheory`/`FieldSystem`/`PoincareAction`/`EnergyMomentumMeasure` |
| `FieldLabels`, `FieldSystem`, `Faithful` | carrier + smeared field `field : carrier →ₗ[ℂ] TestFunction →ₗ[ℂ] (domain →ₗ domain)` + `vacuum`, `vector`, `vacuumExpectation` | carriers exist, but no "color charge" predicate on them |
| `PoincareAction.Symmetry`, `onLabels` | label-space symmetries; translations only in `translationCompatibility` | no gauge-type continuity/covariance requirement |

### Layer 2 — lattice side (`PublicWilson.lean`)

| Line | Object | Statement shape |
|---|---|---|
| 11–13 | `Site`, `Configuration`, `Directions` | lattice links valued in `g.image` |
| 20 | `plaquette` | `1 − trace.re/(n+1)` per site×direction |
| 25 | `wilsonEnergy` | sum of plaquettes over the lattice |
| 29 | `wilsonLaw` | Boltzmann `withDensity` measure against Haar |
| 35 | `WilsonFamily g` | `period`/`denominator` (strictly increasing `ℕ+`)/`beta`/`haar`/`Token`/`insertion` |
| 50–51 | `mesh`, `place` | lattice-spacing `mesh N → 0`; site → continuum point |
| 54 | `finiteMoment` | finitely many `Token` insertions at separated sites |
| 79 | `smear` | correlation of finitely many smeared insertions |
| 85 | `Converges` | volume-order stability of smeared correlations as `N → ∞` |

### Layer 3 — hierarchy and the "nonfree" clause (`ChallengeSpec.lean`)

| Line | Object | Confinement-relevant content |
|---|---|---|
| 12 | `WilsonRegularity C` | running `β N p / log(mesh N)⁻¹ → slope` (lattice asymptotic freedom); gauge **`invariant`** forcing orbit-constness; finite stencil `localSupport` |
| 24 | `Hierarchy C` | the bridge: `centeredTrace : Field 4` tagged by the Wilson family |
| 70 | `OperatorProductExpansion` | short-distance fusion rules of gauge-invariant fields |
| 117 | `Reconstructed` | Wightman reconstruction from the continuum limits |
| 146, 149 | `timePair`, `traceTwo r` | `⟨Ω, φ(f)Ω⟩`-type two-point of `centeredTrace` at Euclidean time separation `r` |
| 152–165 | `Mode`, `Track`, `wickProfile` | candidate Wick-germ profiles for the two-point at `0⁺` |
| 168 | `TraceTest` | **the "nonfree" node**: `centered` (`⟨Ω, φ(f)Ω⟩ = 0` for trace), `amplitudePositive` (`3 dim g.lieAlgebra/π⁴ > 0`), `shortDistance` (`r⁸ log²(r⁻¹) · traceTwo r → 3 dim g/π⁴`), and `excludes` (`¬ traceTwo =ᶠ[𝓝[>] 0] wickProfile terms` for all finitely many `(ℂ × Track)` profiles) |
| 177 | `Properties order` | `wilson : C.Converges`, `reconstruction : Reconstructed`, `ope`, `nonfree : TraceTest` |
| 186 | `JointExistence` | `∀ g, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p strictMono, ∃ q, ∃ T : Hierarchy C, T.Properties (p∘q)` |

This is the whole confinement methodology as specified: build a Wilson family on the lattice, prove its regularity (asymptotic freedom + gauge invariance + locality), prove its smeared correlations converge, reconstruct a Wightman theory, derive an OPE, and check the trace-channel two-point has a non-Wick short-distance signature.

---

## Part II — Expressibility audit: what the public language can even say

Before evaluating whether the methodology *succeeds*, one must check whether it can even *state* confinement. Four findings, all structural:

### 1. `GaugeGroup` is an orphan

`GaugeGroup`/`IsSimple` are defined in `PublicTheory.lean`, but:

- `FieldSystem` has no gauge structure field — the field is `field : Labels.carrier →ₗ[ℂ] TestFunction →ₗ[ℂ] (domain →ₗ domain)` with no `U ↦ U·field·U⁻¹` action;
- `PoincareAction.Symmetry` acts on labels via `onLabels : Symmetry → Labels.carrier ≃ₗ[ℂ] Labels.carrier`, but `translationCompatibility` constrains translations only — no gauge-type symmetry class exists;
- `EnergyMomentumMeasure` is defined per-carrier (`diagonal : carrier → Measure`) with no gauge constraint;
- every insertion in `WilsonFamily.Token` and `Hierarchy` is gauge-invariant **by construction** (`WilsonRegularity.invariant`).

Consequently the sentence "label ℓ carries color charge" is not expressible in the public language: there is no representation of the gauge group on `Labels.carrier` whose nontriviality could witness it.

### 2. All correlation data are vacuum-side

`smear` (PublicWilson:79), `finiteMoment` (54), `Reconstructed`, and every `TraceTest` field are expectations of finitely many insertions **in the vacuum**. There is no public clause quantifying states, sectors, one-particle spaces, or `S`-matrix data. Gauge-invariant vacuum correlations are exactly the observables of the *confined* theory — they are blind to whether non-gauge-invariant sectors exist in the Hilbert space.

### 3. "Free" must be re-stated spectrally

Because the public language has no one-particle-space or Wigner-classification notion, the only faithful formalization of "quark exists freely" is **spectral**: the momentum-space (`EnergyMomentumMeasure.diagonal`) measure of vacuum excitations `φ_ℓ(f)Ω` charges the mass shell `massShell m = {p ∈ forwardCone | minkowskiSquare p = m², p ≠ 0}` for some `m > 0`. This is `FreeLabel` (Confinement.lean:119), and `ConfinedLabel := ¬ FreeLabel` (124). This is strictly a *surrogate*: it detects whether vacuum excitations of the label propagate freely on-shell, which is the right necessary trace of a free colored particle (Reconstruction/interpretation), but it is derivable from the theory's own spectral data.

### 4. The gauge-side interface must be introduced to say anything at all

`Confinement.lean:134` introduces `GaugeIntertwinesTypeDef T gauge`: a representation `ρ : ↥gauge.image → Labels.carrier ≃ₗ[ℂ] Labels.carrier`, unitaries `U : ↥gauge.image → H.Operator` fixing the vacuum, mapping the domain into itself, with covariance `U g (φ_ℓ(f) v) = φ_{ρ(g,ℓ)}(f) (U g v)`, and **separation**: `ρ(g,ℓ) ≠ ρ(g,ℓ')` for distinct labels tested by smeared excitations. This is the minimal interface without which color charge is undefinable — and it is exactly what the public API lacks.

---

## Part III — Six routes to confinement in the stated methodology, evaluated simultaneously

### Route 1 — mass gap ⇒ confinement (spectral argument). **RULED OUT.**

Idea: the challenge's gap condition kills all spectrum in the low region; a free quark's spectral support near `p = 0` would violate it; hence no free quarks.

What survives analysis: `free_label_mass_ge_of_massGap` (Confinement.lean:237) — the one part of this route that **is provable**: under the gap condition at `m`, if a vacuum-centered excitation charges the shell `massShell μ` with `0 < μ < m`, contradiction. Hence a *spectrally free* label can only have on-shell vacuum excitations with masses `≥ m`.

Why the route fails: the gap excludes only **light** free carriers. Nothing in the public language bounds the mass of a colored label. A free colored sector of mass exactly `m` (or heavier) has vacuum spectral support inside `LowRegion mᵃᶜ` and satisfies every clause. Formally: `FreeLabel` at mass `≥ m` is consistent with `GapCondition T m` — the proof of the positive result stops precisely where the unprovable strengthening would begin. The route is quantitatively too weak *by design of the challenge statement*, which never requires the gap to be at arbitrarily low mass for all labels.

### Route 2 — clustering / unique vacuum ⇒ no free colored states. **RULED OUT.**

Idea: `W0.uniqueVacuum` plus clustering forces all non-vacuum states to be massive composites; colored states would violate clustering.

Fails at three points: (i) `W0`'s clustering is a statement about vacuum correlations — again gauge-invariant observables; (ii) a free massive field *does* cluster (its vacuum two-points factorize at spacelike separation by standard spectral estimates); (iii) `uniqueVacuum` concerns the translation-invariant vector in `H`, and in the direct-sum construction below the new block `K` contains no translation-invariant vector, so uniqueness survives. Route dead.

### Route 3 — superselection / Gauss law. **CONDITIONAL — the only live bridge; ruled out *publicly*.**

The true mechanism in QCD: physical states are gauge-invariant by Gauss law; a colored one-particle state would need a non-gauge-invariant vector in the physical Hilbert space, which does not exist; plus energy diverges in the limit (color flux tube tension) so asymptotic colored states have infinite mass.

In the public language this appears as the conditional chain proved in `Confinement.lean`:

- `ShellNeutral T gauge U` (150): on-shell vacuum excitations are gauge-fixed, `U g (φ_ℓ(f)Ω) = φ_ℓ(f)Ω` whenever they charge the shell — the Gauss-law datum;
- `freeLabel_gauge_trivial` (177): **proved** — every spectrally free label is gauge-fixed, `∀ g, ρ(g,ℓ) = ℓ`;
- `confined_of_colorCharged` (189): **proved** — a color-carrying label (`ColorCharged`, i.e. `∃ g, ρ(g,ℓ) ≠ ℓ`) is confined;
- `free_means_colorless` (263): contrapositive summary — freeness forces color-neutrality.

This is a genuine theorem *given the interface* — but the interface (`GaugeIntertwinesTypeDef` + `ShellNeutral`) is precisely the datum the public API lacks. No lattice- or OPE-side clause of Part I implies `ShellNeutral`; `WilsonRegularity.invariant` concerns the *lattice* observables, not the Hilbert-space action of the gauge group. So the route is correct mathematics but **not part of the stated methodology**; publicly it is ruled out as unavailable.

### Route 4 — Wilson area law / string tension. **RULED OUT.**

The physical statement underlying confinement on the lattice: Wilson loops obey an area law (`⟨W(C)⟩ ~ e^{−σ·Area}`), i.e. static quarks are linearly confined with nonzero string tension.

The challenge's lattice layer (`PublicWilson.lean`, `WilsonRegularity`) contains **no area-law clause**: `wilsonEnergy` is a bulk energy density (plaquette sum), `WilsonRegularity` constrains the *running coupling* (`beta` vs `log(mesh)`⁻¹ — asymptotic freedom), gauge invariance of insertions, and a finite stencil. There is no Wilson-loop observable, no loop expectation, no tension parameter anywhere in `PublicWilson.lean` or `ChallengeSpec.lean`. Moreover, quark legs are syntactically forbidden: every `Token`/insertion is gauge-invariant (element of the center trace channel), so no open Wilson line ever appears. The methodology is blind by construction to the observable that defines confinement on the lattice.

### Route 5 — the `TraceTest` "nonfree" clause (Wick-germ exclusion). **RULED OUT.**

The clause that looks like a confinement statement. Decomposed (ChallengeSpec:168) it contains four fields:

- `centered`: the trace channel has zero vacuum one-point — normalization, confinement-neutral;
- `amplitudePositive`: `3·dim g.lieAlgebra/π⁴ > 0` — a positivity fact, unconditional, confinement-neutral;
- `shortDistance`: `r⁸ log²(r⁻¹)·traceTwo r → 3 dim g.lieAlgebra/π⁴` as `r → 0⁺` — an anomalous-dimension statement for the **single gauge-invariant trace channel**; it *presupposes* interacting short-distance behavior (the `r⁸ log²` factor is the assumed interaction signature, a hypothesis inside the test, not a conclusion);
- `excludes`: `traceTwo` is not asymptotic to any finitely-generated `wickProfile` — a germ-level (at `0⁺`-only) exclusion of free-particle-type profiles **in that one channel**.

Why it cannot yield confinement: (i) it constrains one gauge-invariant vacuum channel, and a free colored sector contributes *nothing* to trace-channel vacuum correlations (its insertions into Ω⊕0 all vanish) — so both `shortDistance` and `excludes` survive the deviation unchanged; (ii) it is a germ statement at `0⁺` and says nothing about on-shell propagation at `m > 0`; (iii) "non-Wick at short distance" is a statement about *scaling dimensions/OPE*, not about the existence of free asymptotic colored states — it would also hold in theories with free colored sectors plus interacting gauge-invariant composites. Route dead: it is a test of *interaction*, mislabeled `nonfree`.

### Route 6 — transfer matrix / Hamiltonian positivity. **RULED OUT (out of spec scope).**

The rigorous lattice route (Osterwalder–Schrader reconstruction + transfer matrix) could in principle connect Euclidean lattice positivity to a Hamiltonian with a Gauss-law constraint. The challenge contains no OS-positivity axiom, no transfer matrix, no Hamiltonian constraint clause — `Hierarchy` bridges only through smeared vacuum correlations and `Reconstructed`. Nothing to evaluate; absent from the specification.

### Tally

| Route | Status | Blocking object |
|---|---|---|
| 1. Mass gap spectral | **RULED OUT** (only light-freeness excluded — proved) | no mass bound on colored labels |
| 2. Clustering | **RULED OUT** | vacuum-side, gauge-invariant only |
| 3. Superselection/Gauss | **CONDITIONAL** (proved given interface) / ruled out publicly | `ShellNeutral` not implied by any clause |
| 4. Wilson area law | **RULED OUT** | no loop/tension clause in spec |
| 5. `TraceTest` | **RULED OUT** | one channel, germ 0⁺, interaction assumed |
| 6. Transfer matrix | **RULED OUT** | absent from specification |

Every route fails or reduces to Route 3's missing datum.

---

## Part IV — The decisive structural obstruction: sector invisibility

The definitive argument, expressible in the public language:

Let the (confined) candidate theory `T` satisfy every clause of `JointExistence` — `WilsonRegularity`, `Converges`, `Reconstructed`, OPE, and `TraceTest`. Construct the Hilbert-space direct sum `H' = H ⊕ K`, with `K` the one-particle space of a free massive scalar of mass `m > 0` carrying a nontrivial color representation: field `φ_ℓ'(f) := φ_ℓ(f) ⊕ φᶠʳᵉᵉ(f)` acting on `K` in the `ρ`-representation with `ρ` nontrivial (possible since `g.IsSimple`, `dim g.lieAlgebra ≥ 2`), vacuum `Ω' := Ω ⊕ 0`.

Verification that every clause survives:

1. **Vacuum correlations unchanged.** For any finite tuple of insertions, `⟨Ω', φ⋯(f)Ω'⟩ = ⟨Ω, φ⋯(f)Ω⟩ + ⟨0, ⋯0⟩ = ⟨Ω, φ⋯(f)Ω⟩`, because every insertion's `K`-block hits `0` at the right end. So `smear`, `finiteMoment`, `Converges`, `Reconstructed`, `OperatorProductExpansion`, and all four fields of `TraceTest` are identical to those of `T`.
2. **Translation invariance / `W0`.** The `K`-block vacuum `0` is fixed by translations (it is zero), and `Ω ⊕ 0` is the unique translation-invariant unit vector in `H ⊕ K`: a translation-invariant vector in the free massive block `K` would be a translation-invariant vector of the scalar one-particle space, which does not exist for `m > 0` (no zero-momentum-normalizable state). So `uniqueVacuum` survives.
3. **Energy-momentum measure.** The `H`-block projection structure is unchanged on the `Ω ⊕ 0`-subspace relevant to vacuum data; the free block only *adds* spectral support off the vacuum sector.
4. **But confinement now fails maximally:** the label extending ℓ into the colored block has vacuum excitations `φ_ℓ'(f)(Ω ⊕ 0) ∈ K` with spectral measure concentrating on `massShell m` — i.e. a **free, colored, propagating excitation** in the sense of `FreeLabel`.

Hence:

> **No conjunction of the hypotheses in Part I can imply confinement.** Any evaluation method that consumes only those hypotheses returns the same verdict for the confined theory and for its free-colored direct-sum extension; confinement separates them; therefore no such method can establish confinement.

This is not a gap in the *estimates* — it is a gap in the *hypotheses*, and no amount of additional analysis within the stated methodology can close it. The methodology can only be rescued by **extending** the specification: adding a gauge-intertwining interface (`GaugeIntertwinesTypeDef`) with the shell-neutrality datum (`ShellNeutral`), in which case Route 3's proved chain (`freeLabel_gauge_trivial` → `confined_of_colorCharged`) applies — and the free-colored extension of Part IV is then no longer admissible because it violates `ShellNeutral` (its colored excitations are *not* gauge-fixed).

This is exactly parallel to the mass-gap finding: there, `LorentzIntertwines` + the wedge datum was the missing input (`MassGapScenarios.md` §XIII, `MassGapProof.md` axiom node); here, the gauge-intertwining + shell-neutrality datum is the missing input.

---

## Part V — What `Confinement.lean` proves (machine-checked companion)

All declarations in namespace `YangMills`; compiles against the repo's public API (`import YangMills.PublicTheory`, wheel-of-Mathlib pin of this branch); **0 errors, 0 warnings, 0 `sorry`, 0 `axiom`**.

| § | Declaration | Line | Content |
|---|---|---|---|
| 1 | `timeL`, `spatialL`, continuity lemmas, `closed_forwardCone`, `measurableSet_forwardCone`, `continuous_minkowskiSquare` | 50–72 | geometry (copied patterns from `MassGap.lean`) |
| 2 | `massShell`, `measurableSet_massShell` | 76–90 | the positive-mass shell `{p ∈ forwardCone ∧ minkowskiSquare p = m², p ≠ 0}` is measurable |
| 3 | `excitation`, `diagonal_zero_measure`, `excitation_nonzero_of_free` | 94–113 | vacuum excitations `φ_ℓ(f)Ω` and their spectral measures |
| 4 | `FreeLabel`, `ConfinedLabel` | 119–127 | spectral freeness of a label; confinement as its negation |
| 5 | `GaugeIntertwinesTypeDef`, `ShellNeutral`, `ColorCharged` | 134–161 | **the missing interface**, made explicit |
| 6 | `gauge_excitation` | 164 | covariance of vacuum excitations under `U` |
| 7 | `freeLabel_gauge_trivial` | 177 | **theorem** — free ⇒ gauge-fixed (colorless) |
| 8 | `confined_of_colorCharged` | 189 | **theorem** — color-charged ⇒ confined |
| 9 | `LowRegion`, `GapCondition`, `lattice_set`, `pow_le_of_lt_positive`, `inter_massShell_lowRegion` | 200–229 | mass-gap side (duplicated from `MassGap.lean`, which is not a library root) |
| 10 | `free_label_mass_ge_of_massGap` | 237 | **theorem** — under the gap, free labels have masses `≥ m` |
| 11 | `free_means_colorless` | 263 | contrapositive summary |

Axiom audit (`#print axioms` on the files' theorems):

```
freeLabel_gauge_trivial      [propext, Classical.choice, Quot.sound]
confined_of_colorCharged     [propext, Classical.choice, Quot.sound]
free_means_colorless         [propext, Classical.choice, Quot.sound]
free_label_mass_ge_of_massGap [propext, Classical.choice, Quot.sound]
inter_massShell_lowRegion    [propext, Classical.choice, Quot.sound]
measurableSet_massShell      [propext, Classical.choice, Quot.sound]
```

Standard Lean axioms only — nothing is assumed. In particular, unlike `MassGapProof.md`'s `[B]`-node, **no confinement datum needed to be postulated**: the conditional chain closes completely, and the unconditional claim is simply not derivable (Part IV).

---

## Part VI — Final verdict

| Question | Answer | Evidence |
|---|---|---|
| Can the stated methodology imply "quarks cannot exist freely"? | **NO** | Part IV direct-sum deviation preserves every hypothesis |
| Which hypothesis class is the culprit? | vacuum correlations of gauge-invariant insertions | Part II.2; `Properties`/`JointExistence` (ChallengeSpec:177/186) |
| Is the mass gap sufficient for confinement? | No — it excludes only free carriers with masses `< m` | `free_label_mass_ge_of_massGap` (proved) |
| Is any confinement mechanism expressible? | Yes, conditionally, via an interface the API lacks | `GaugeIntertwinesTypeDef` + `ShellNeutral`; `freeLabel_gauge_trivial`, `confined_of_colorCharged` (proved) |
| Is the `TraceTest` `nonfree` clause a confinement statement? | **No** — it is a short-distance/interaction statement in one gauge-invariant vacuum channel | Part III Route 5 |
| Verdict on the methodology | **RULE OUT** — cannot establish confinement; only its extended (gauge-intertwined, shell-neutral) successor could | Parts III, IV, VI |

---

## Appendix — Verification

```bash
cd /workspace/github__yang-mills-group__OpenAI-YM-20261028
export PATH="$HOME/.elan/bin:$PATH"
lake env lean Confinement.lean
# exit 0, no output — 0 errors, 0 warnings, 0 'sorry', 0 'axiom'
```

Axiom audit (on a copy with an appended `#print axioms` block): all six audited theorems print `[propext, Classical.choice, Quot.sound]`; exit code 0.

Compiler/environment: Lean 4 with Mathlib snapshot `81a5d257c8e410db227a6665ed08f64fea08e997`; `lakefile.toml` root of this branch; `Confinement.lean` compiled via `lake env lean` (it is not a library root; `MassGap.lean` defs it needs are duplicated, see Confinement.lean:198–204).

**Cross-references.** Mass-gap analysis: `MassGapScenarios.md` (Parts I–XIII, incl. §2 low region, §11 spectral surrogate, §15 `LorentzIntertwines`, §48/§56 route tallies, Part XIII verdict). Lean walkthrough: `MassGapProof.md` (single `sorry`-free source with the explicit `[B]`-axiom node). API `PublicTheory.lean` untouched throughout.
