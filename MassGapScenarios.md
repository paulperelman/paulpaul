# Conditions for a mass gap in the Wilson Yang–Mills hierarchy

STATUS: analysis note. [YangMills.jointExistence](ChallengeSpec.lean) is
proved and audited; the README records that a positive mass gap is outside its
scope. This note fixes the mass-gap statement in the language of the public
definitions, enumerates **every** mechanism by which the constructed theory can
fail to have one, checks each scenario against the four conclusions that are
actually proved, and states the conditions under which a mass gap follows. The
mathematical content is organised in three rigour levels:

- **[A]** statements derivable now, by standard functional analysis, from the
  already-proved public signatures (`W0`–`W3`, `EnergyMomentumMeasure`,
  `Hierarchy.Properties`);
- **[B]** standard QFT theorems whose Lean formalisation needs a
  matrix-valued Källén–Lehmann / strip-of-analyticity layer beyond the current
  repo (proof sketches given);
- **[C]** genuinely open analytic input — the actual remaining mass-gap
  problem.

No theorem of the repository is modified. Nothing here claims a proof of the
mass gap.

---

## 1. The fixed data

Throughout, fix a gauge group `g : GaugeGroup` with `g.IsSimple`, a Wilson
family `C` and a hierarchy `T : Hierarchy C` with `T.Properties order`
(`ChallengeSpec.lean:186`). What is available, by identifier:

| Object | Where | Content used here |
|---|---|---|
| `theory : WightmanTheory H labels` | `Hierarchy.theory` | the selected continuum phase |
| `theory.Axioms` | `W0`–`W3`, via `Reconstructed.axioms` | covariance, spectrum condition, unique vacuum, cyclic vacuum, temperedness, locality |
| `theory.energyMomentum` | `EnergyMomentumMeasure` (`PublicTheory.lean:180`) | the PVM `projection : Set Spacetime → H.Operator`; scalar spectral measures `diagonal ψ` pinned to it by `diagonalIdentity` |
| `W0.positiveEnergy` | `PublicTheory.lean:274` | `projection forwardConeᶜ = 0`, i.e. every spectral measure is supported in the closed forward cone `forwardCone = {x | ‖spatial x‖ ≤ time x}` |
| `W0.uniqueVacuum` | `PublicTheory.lean:276` | translation-invariant vectors are exactly the scalar multiples of the vacuum |
| `W1.domain.cyclicVacuum` | `PublicTheory.lean:130` | the field words applied to the vacuum span a dense subspace (the domain) |
| `Reconstructed` extras | `ChallengeSpec.lean:117` | `characterContinuity`, `mixture`, `fullSupport`, `characterCompact` |
| `OperatorProductExpansion` | `ChallengeSpec.lean:70` | all-orders separated OPE with **integer** weights `T.weight` and coefficient bound `r^(j − weight a − ε)` |
| `TraceTest` | `ChallengeSpec.lean:168` | vacuum-centered grade-4 trace; `shortDistance` amplitude `3·(finrank ℝ g.lieAlgebra)/π⁴ > 0`; `excludes` against finite sums of mass-shell `Mode.kernel` profiles `∝ exp(−r·E)`, `E = √(mass² + ‖p‖²)` |
| `WilsonRegularity` | `ChallengeSpec.lean:12` | UV origin: fixed stencil, running slope strictly positive (`2·Pert.Asymptotics.b0`, see `HierarchyBridge.lean`) |
| `YM.OS.Semigroup` / `ground` | `YM/OS/Core.lean` | reflection-positive heat semigroup `E t` on the same hierarchy, and its invariant subspace `ground` — built “without spectral theory” |
| `YM.Spectral.Projection` / `Frequencies` | `YM/Spectral/` | PVM support criteria by tested supports |
| `YM.TraceExtension.Wick.Refute` | header | the exact limit of `excludes`: no claim against a *continuous-mass* generalized free field |

Two structural remarks drive everything below.

**(i) The spectrum condition closes the cone.** `W0.positiveEnergy` says the
projection of the *complement* of `forwardCone` vanishes; hence for every
state ψ the measure `diagonal ψ` is supported in the closed forward cone, where
`minkowskiSquare p ≥ 0`. The dangerous part of the spectrum is therefore
exactly the vertex-neighbourhood inside `forwardCone`.

**(ii) The relevant spectrum is the invariant `p²`, not the energy.** On
`forwardCone`, `√(minkowskiSquare p) ≤ time p`, with equality exactly on the
rest ray of a timelike orbit. This disparity (energy vs invariant mass) is
what separates the scenarios below; §4.2 shows it has a sharp consequence.

---

## 2. The target, in the repository’s own language

```lean
/-- Closed part of the forward cone below the would-be mass shell,
excluding the vertex. Closed, hence Borel; supports live here by W0. -/
def LowRegion (m : ℝ) : Set Spacetime :=
  {p | p ∈ forwardCone ∧ minkowskiSquare p ≤ m ^ 2 ∧ p ≠ 0}

/-- Mass gap in the public language: the joint energy–momentum PVM
compressed to the orthocomplement of the vacuum avoids `LowRegion m`.
The projection has values in `H.Operator`; vanishing on every state is
vanishing as an operator by `EnergyMomentumMeasure.selfAdjoint`. -/
def MassGap (T : WightmanTheory H Labels) (m : ℝ) : Prop :=
  0 < m ∧ ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
    T.energyMomentum.projection (LowRegion m) ψ = 0
```

*(Lean fragments in this note are written against the signatures of
`PublicTheory.lean` and are uncompiled — see §6.)*

Equivalently (and for formalisation preferably): `μ_ψ(LowRegion m) = 0` for all
ψ ⊥ Ω, where `μ_ψ := theory.energyMomentum.diagonal ψ`, using
`diagonalIdentity`.

**Lemma 2.1 (no vacuum atom on the orthocomplement). [A]**
For ψ ⊥ Ω, `projection {0} ψ = 0`.

*Proof.* Let `c-state := projection {0} ψ`. `projection {0}` is a projection
(`selfAdjoint`, idempotent from `intersection`), so
`inner (projection {0} ψ) (projection {0} ψ) = inner ψ (projection {0} ψ)`.
If nonzero and ψ ⊥ Ω, then `projection {0} ψ` is a translation-invariant unit
vector, so by `W0.uniqueVacuum` it is a nonzero multiple of Ω while being a
scalar multiple of ψ composed with a projection — combine: ⟨ψ, cΩ⟩ = c⟨ψ,Ω⟩ = 0
forces `‖projection {0} ψ‖ = 0`, contradiction. ∎

So the vertex belongs to the *operator* kernel on Ω⊥; the topological support
may still accumulate there — that is precisely scenarios A2/A3.

---

## 3. Exhaustive failure scenarios

### 3.1 The support trichotomy — why the list below is complete

For the compressed PVM `E⊥ := E|_{Ω⊥}` (Borel functional calculus of
`theory.energyMomentum` on the orthocomplement), define

```
m*(T) := sup { inf √(minkowskiSquare p) : p ∈ supp μ_ψ, ψ ∈ Ω⊥, ‖ψ‖ = 1 }.
```

`MassGap(T, m)` holds **iff** `m*(T) ≥ m`. Its failure means: for every m > 0
some spectral weight of Ω⊥ sits in `LowRegion m`. Take `mₙ ↓ 0` and
unit ψₙ ∈ Ω⊥ with `μψₙ(LowRegion mₙ) > 0`; write νₙ for the renormalised
restriction of `μψₙ` to `LowRegion mₙ`. Each νₙ is a probability measure
supported in `forwardCone` with `minkowskiSquare ≤ mₙ`. Any subsequential
vague accumulation point ν of {νₙ} lives on
`forwardCone ∩ {minkowskiSquare ≤ 0}` — the light cone. Split by whether mass
escapes to infinity:

- **Light-form.** Weight survives on `{p ≠ 0 : minkowskiSquare p = 0}` at
  finite energy, or the νₙ concentrate near lightlike points of unbounded
  energy. In the second case, boost covariance of the support (Level [B];
  from `W2.fieldCovariance` by the standard PVM-covariance reconstruction)
  produces rest points `(√p², 0)` in the support with `√p² → 0`, i.e. the two
  cases are not independent; both are manifestations of *massless spectrum*.
- **Vertex accumulation without light-form.** Mass escapes toward `p = 0`;
  by Lemma 2.1 no atom may sit at the vertex, so the weight is either an
  atom tower (scenarios A2) or diffuses (A3).

This dichotomy is exhaustive: a finite Borel measure on the forward cone with
invariant-mass infimum 0 either has its low-`p²` mass carried by atoms
approaching the vertex or the light shell (A1/A2), or by a non-atomic tail
(A3); and if witnesses require more than one phase or one volume limit, that
is the construction’s own doing, catalogued as A4/A5. The list A1–A7 below is
therefore complete *relative to the fixed data*: nothing in a Wightman theory
satisfying `W0`–`W3` can be gapless in any other way.

### 3.2 The catalogue

For each scenario: definition, spectral signature, and the signature forced on
large-distance Euclidean correlations. Decay formulas are for the scalarised
stationary two-point with Källén–Lehmann density ρ(s) on
`s = minkowskiSquare`; the kernel identity

```
D(r)  =  ∫₀^∞ ρ(s) · (√s / 4π²r) · K₁(r√s)  ds          (equal-time spatial distance r)
```

(with `D ≍ r⁻²` for a light-shell atom and `ρ ~ s^α ⟹ D(r) ≍ C_α r^{−(2α+3)}`
from `∫ t^{2α+2} K₁ = 2^{2α+1} Γ(α+2)Γ(α+1)`) is Level [B] for matrix-valued
measures, elementary for scalars.

| ID | Scenario | Spectral signature | Correlation signature |
|---|---|---|---|
| **A1** | Massless particle (light-form) | spectral weight (atom or cut) on `{p² = 0, p ≠ 0}`; allowed by `W0` at any energy, since lightlike boost orbits `{p⁰ = ‖p⃗‖ ≥ c}` are closed and Poincaré-invariant | `D(r) ~ 1/4π²r²` (scalar shell); polynomial, never exponential with a positive rate bounded away from the shell |
| **A2** | Atomic mass tower | pure-point eigenvalues with `p²ₙ ↓ 0`; covariance permits a closed invariant tower | `D(r) ~ Σ wₙ (√sₙ/4π²r) K₁(r√sₙ)`; `lim (1/r) log D = 0` — arbitrarily slow, e.g. `exp(−r/log r)` for `mₙ = 1/log n` |
| **A3a** | Continuous spectrum with finite-order density | non-atomic support touching `s = 0`, `ρ(s) ~ c s^α`, `α ≥ 0` | `D(r) ≍ C_α r^{−(2α+3)}` (e.g. flat density: `r⁻³`) |
| **A3b** | Continuous spectrum, density flat to high order | `ρ(s) = e^{−a/s}`-type | all algebraic terms vanish yet the *rate* is still 0: `D(r) ~ exp(−2√(ar))·r^{−β}` — **exponential clustering can coexist with no mass gap** (see §4.2) |
| **A4** | Character dilution | the gap function `χ ↦ m(χ)` on the compact `Character` space is pointwise positive but `inf = 0` | the unselected phase (`mixture`, `fullSupport`) shows arbitrarily slow tails; the `selected` phase may still be massive |
| **A5** | Volume-subsequence selection | different refinement subsequences in `JointExistence` select different phases; a gapless one is selectable | not visible in any single hierarchy; a statement quantified over the construction |
| **A6** | Trivial (Gaussian) continuum limit | the only spectrum is free Wick | `traceTwo` would equal a `wickProfile` — **excluded** by `TraceTest.excludes` for the trace channel, together with the interacting `shortDistance` amplitude `3·dim 𝔤/π⁴` |
| **A7** | Vacuum degeneracy / θ-sector splitting | several invariant vectors | **excluded** by `W0.uniqueVacuum` for the constructed theory; residual risk only via A5 (selection multiplicity) |

### 3.3 Consistency matrix against the four proved conclusions

| Scenario | `WilsonRegularity` (UV) | `W0`–`W3` | `OperatorProductExpansion` (short distance) | `TraceTest` |
|---|---|---|---|---|
| A1 massless | compatible | compatible | compatible | compatible |
| A2 tower | compatible | compatible | compatible | compatible |
| A3a/A3b continuum | compatible | compatible | compatible | compatible (`Wick/Refute.lean` explicitly disclaims continuous-mass GFF) |
| A4 character inf = 0 | compatible | compatible for `selected` | compatible | compatible |
| A5 subsequence selection | compatible by construction | compatible | compatible | compatible |
| A6 trivial limit | tension with slope `2·b₀ > 0` | compatible | compatible | **blocked** (trace channel) |
| A7 degeneracy | compatible | **excluded** | compatible | compatible |


**Footnote on the detailed theorem.** The construction theorem
`YM.Nonperturbative.Headline.WilsonExistence` proves, beyond the public four,
`TraceExclusions` (`YM/Nonperturbative/HeadlineSpec.lean`) with three further
countertests for the physical trace signal in the selected phase: `wick`
(exclusion of every finite Wick-palette description), `maxwell` (exclusion of
Maxwell Fock realizations with physical-wave, vacuum and translation
conditions) and `invariant` (exclusion of measure-averaged invariant-sector
realizations). These strengthen the A6 row below and block the
*free-photon-like* realization of the trace channel; they do not touch A1 in
its interacting form, nor A2–A5 — see §10.

**Reading of the matrix.** Every rigorous input in the repository — Wilson
origin, W0–W3, the all-orders separated OPE, and the trace non-freeness — is
*short-distance* or *algebraic*. All mass-gap failure mechanisms A1–A5 live at
large distance or large volume. Hence:

> **Proposition (level [A]).** The four proved public conclusions, taken
> alone, are logically consistent with every scenario A1–A5. No contradiction,
> and therefore no mass gap, can be extracted from them without new analytic
> input at one of the certificates in §5.

This is the precise sense in which the existing construction is agnostic, and
it is a derivable statement (each row is decidable from the stated signatures).

---

## 4. The rate calculus

### 4.1 What each observable actually tests

Let `ψ = field ℓ f Ω` (or any vector in the domain) and consider the Euclidean
correlations at large distance, read off the hierarchy directly:

- **Pure-time separation** `D(τ)` at fixed, spatially-integrated smearing
  (zero-momentum two-point): `D(τ) = ∫ e^{−τ·p⁰} dμ(ZM-weighted)`;
  decay **rate = inf p⁰ over the support** of the involved spectral measure.
  Elementary Laplace analysis; one-sided certificates are Level [A].
- **Equal-time spatial separation** `D(r)`: rate = `inf √(p²)` *after* the
  fiber-integral regularity of the strip argument — Level [B] (§4.2).
- **Generic separated points**: rates interpolate; only the two extremes above
  have clean spectral readings.

### 4.2 Two sharp structural facts

**Fact 4.2.1 (energy gap vs invariant gap; level [A] modulo [B] covariance).**
Assume the PVM support on Ω⊥ is invariant under the proper orthochronous
Poincaré action (Level [B]: standard derivation from `W2.fieldCovariance`,
since `W0.spectralRepresentation` pins the measures to the PVM). Boost orbits
of *timelike* spectral points contain the rest point `(√(p²), 0)`. Therefore:

```
invariant mass gap m  ⟺  energy gap m on Ω⊥   ∧   no light-form (A1).
```

The energy gap alone does **not** give the mass gap: lightlike orbits based at
`p⁰ = c ≥ m` (a “massless particle with momentum ≥ c”) keep the energy gap
while `p² = 0` violates it. Conversely the invariant gap forces the energy gap
(trivially, `p⁰ ≥ √p²` on the cone) and the light-form exclusion.

**Fact 4.2.2 (spatial exponential clustering is necessary but not sufficient;
level [B] with the strip argument).**
For scalarised two-points:
- (gap ⟹ clustering) If the K-L support avoids `p² < m²`, the spatial Fourier
  integrand extends analytically to `‖Im p⃗‖ < m` (the Lightcone branch-point
  condition `|p⃗|² − |ξ|² + m² = 0` has no solution for `|ξ| < m`), so
  Paley–Wiener–Schwartz gives `|D(r)| ≤ C r^{N} e^{−m r}`. The Fourier–Laplace
  parts of this argument are the domain of `YM/Paley`.
- (clustering ⟹ Support gap, one-sided) Mass of ν on a shell `s ≈ s₀` forces
  `D(r) ≥ (shell contribution) ∝ √s₀ e^{−√s₀ r}`, which beats `e^{−m r}` for
  every `√s₀ < m` — **provided the shell carries no oscillatory cancellation
  across the p⁰-fiber**, which holds for the positive diagonal measures and for
  the zero-momentum projection (§4.1), and fails in general.
- (no exponential converse) Scenario A3b: `ρ(s) = e^{−a/s}` has support
  touching 0, yet the two-point decays only *sub*exponentially
  (`exp(−2√(ar))·r^{−β}`), so no exponential rate exists at all; A2 towers
  can be tuned to imitate any prescribed subexponential law.
  The point: **an exhibited exponential upper bound with rate m certifies the
  two-point support gap (and, with §5, the mass gap); a failure to exhibit one
  certifies nothing**, and success of spatial clustering alone still does not
  exclude light-form (A1 with `‖p⃗‖ ≥ c`) without the covariance argument of
  Fact 4.2.1 plus a direct light-form test.

---

## 5. Conditions for a mass gap

Combine §3 and Fact 4.2.1. The exact logico-spectral identity is:

**Theorem 5.1 (decomposition; [A] modulo [B] for boost covariance).**
Fix `m > 0`. `MassGap(T, m)` is equivalent to the conjunction of:

- **C1 (energy gap on Ω⊥).** Precisely:
  `E⊥({p ∈ forwardCone : time p < m}) = 0`.
- **C2 (light-form exclusion).** `E⊥({p | minkowskiSquare p = 0 ∧ p ≠ 0}) = 0`.

and C1, in turn, is equivalent to **uniform Euclidean-time clustering**:

**Theorem 5.2 (clustering certificate; [A]).**
C1 holds for `m > 0` iff there is a finite bound `C` such that for every vector
ψ in the domain (smeared field *words* applied to the vacuum — dense in H by
`W1.domain.cyclicVacuum`), the temporal Laplace moments satisfy
`∫ e^{−τ p⁰} dμ_ψ ≤ C_ψ e^{−m τ}` for all `τ ≥ 0`.
(⇒ is the Laplace bound applied to each diagonal measure; ⇐ the shell lower
bound of §4.2; both use only positivity of the diagonal measures, and the lift
from the dense set to all of Ω⊥ uses continuity of the projections `E(B)` in
the state. Word states are needed because the single-field vectors alone are
not known to span Ω⊥; this is what condition C3 tracks.) In the Euclidean
reflection-positive
picture of `YM/OS`, this is exactly the statement that the heat/transfer
semigroup satisfies `‖E t − E₀‖_{Ω⊥} ≤ e^{−m t}`, i.e. an isolated `ground`
(`YM/OS/Core.lean`), with `ground = ℂΩ` supplied by `W0.uniqueVacuum`.

Hence the **condition list** for a mass gap in this construction:

| # | Condition | Status | Where it would come from |
|---|---|---|---|
| **C1** | Uniform energy gap on Ω⊥ (equiv. Theorem 5.2) | **[C] open** — the analytic core | finite-volume transfer-matrix gap with volume-uniform lower bound (`WilsonFamily`, `Converges`); or a rigorous IR/confinement mechanism. Note a finite-volume gap alone gives nothing: `λ(V) → 0` is exactly scenario A1/A2 materialising through zero modes |
| **C2** | No light-form: `E⊥(light cone ∖ {0}) = 0` | **[C] open**; directly formalizable once assumed (`YM.Spectral.Frequencies` tested-support criteria) | masslessness exclusion is confinement-side input; `TraceTest` does **not** provide it (its `excludes` profile space is entirely massive-shell or, at `mass = 0`, already disclaimed) |
| **C3** | State generation for the certificates | **[A] derivable** | `W1.domain.cyclicVacuum` + continuity of `E(B)`; the hierarchy’s graded label tower (`covers`, `injective`) should be used so that the *lowest* grade bounds all |
| **C4** | Phase uniformity | **[C] open, with a compactness lemma available** | see Lemma 5.3 below; needed only if the gap is claimed for the `none` (Wilson-limit) mixture or if A5 selection is in play |
| **C5** | Threshold bookkeeping | automatic | multi-particle thresholds `≥ n·m₁ ≥ m₁`; only the lowest nonvanishing invariant mass matters, so C1/C2 on the primitive sector propagate |

**Lemma 5.3 (character uniformity; [A] given pointwise input).**
`Character` is compact (`characterCompact`) and `characterContinuity` gives
continuity of separated correlations in χ. Define the per-character gap
`m(χ)` as the decay rate of the per-character zero-momentum two-point
(`m(χ) := sup_{R>0} −(1/R) log |ρ_χ(R)|`, an inf-sup of continuous functions
where defined — note: the *limsup* version needed for a bound is **not**
automatically l.s.c.; that must be supplied). If `χ ↦ m(χ)` is lower
semicontinuous and positive on `support phaseMeasure`, then
`inf > 0`, and the mixture’s gap is the minimum. Failing l.s.c., A4 requires a
separate per-character proof with uniform constants.

**Corollary (what remains; restating the README honestly).** Under the proved
theorem, the mass gap is equivalent to

```
C1 (uniform energy gap)  ∧  C2 (no light-form)
```

together with C3 (free), C4 (when the mixture is in play) and nothing else.
C1 and C2 are the *only* dynamical inputs still missing, and §3.3 shows they
cannot be sourced from the four proved conclusions. The realistic proof paths
map onto existing infrastructure:

1. **Lattice/OS route (C1):** reflection-positive semigroup on the Euclidean
   hierarchy (`YM/OS`, `YM/OS/Semigroup.ground`); verify a volume-uniform
   lower gap. Failure modes to be excluded are precisely A1/A2 low modes.
2. **Direct spectral route (C1 + C2):** the tested-support machinery of
   `YM/Spectral` reduces C2 to countably many projection tests; C1 likewise
   for each `m`.
3. **OPE-assisted route:** the all-orders OPE with integer weights
   (`OperatorProductExpansion`) plus the interacting amplitude
   (`TraceTest.shortDistance = 3·dim 𝔤/π⁴ > 0`, `YM.Gauge.casimir_pos`)
   constrain the short-distance cascade; upgrading these to an *infrared*
   statement requires precisely C1/C2-type input — no shortcut is claimed
   here.

---

## 6. Formalization notes

- The Lean fragments in §2 are written against `PublicTheory.lean`; they are
  **not compiled in this change** (the full YM dependency graph cannot be
  rebuilt here). They introduce only new `def`s of `Prop` — no axioms, no
  `sorry` — and would live naturally in a file `MassGap.lean` importing
  `PublicTheory`.
- Lemma 2.1, Theorem 5.2, and the exhaustion of §3.1 are level-[A] and are
  the natural first formalisation targets; each needs only Mathlib-level
  measure theory (`MeasureTheory.Measure.CharacteristicFunction` is already
  imported by `YM/SNAG/Kernels.lean`) plus the public signatures.
- Fact 4.2.1’s boost-covariance step and the strip argument of Fact 4.2.2 are
  level-[B]; the repo lacks a Källén–Lehmann representation theorem for
  matrix-valued tempered two-points; `YM/Spectral`, `YM/Paley` and
  `YM/AnalyticBridge` are the layers to build it on.
- Nothing here touches the audited verification path (`VerifyJoint.lean`,
  `verification/`); this file is standalone documentation.

## 7. Summary

One sentence per condition:

1. **A mass gap `m` is exactly two spectral statements:** the energy gap
   `E⊥({time p < m}) = 0` (C1) and the absence of lightlike spectral weight on
   Ω⊥ (C2); each is equivalent to checkable certificates (uniform
   Euclidean-time clustering; tested light-cone projections).
2. **Certificates must be uniform**: over states (dense generating set), over
   the character space (compactness + l.s.c., Lemma 5.3), and over volume
   subsequences — otherwise the failure returns through A4/A5 even when every
   individual object decays exponentially.
3. **Exponential spatial clustering is necessary but not sufficient** for a
   mass gap (Fact 4.2.2; near-lightlike and high-order-flat spectra); the
   zero-momentum temporal certificate is the correct equivalence.
4. **Nothing gap-relevant is provable from the four proved conclusions alone**
   (§3.3): the Wilson origin, W0–W3, the all-orders OPE and the trace
   non-freeness are short-distance data, while every mass-gap failure scenario
   is infrared. The open problem is exactly C1 ∧ C2, and the existing
   infrastructure (`YM/OS`, `YM/Spectral`, `YM/Paley`, the graded OPE tower)
   is where those proofs would live.

---

# PART II — second pass: the complete lattice, and the conditions

## 8. The spectral cell lattice: two primitive mechanisms

Part I catalogued scenarios A1–A7. Under the covariance of the PVM support on
Ω⊥ (Level [B]: standard derivation from `W2.fieldCovariance`), the catalogue
collapses to **two primitive failure mechanisms**, and this reduction is exact.

**Theorem 8.1 (primitive-mechanism reduction). [A modulo B-covariance]**
Let `E⊥` be the joint energy–momentum PVM compressed to Ω⊥ and let its
support be invariant under the proper orthochronous Poincaré action. Then:

```
m*(T) = 0   ⟺   [support meets {p ≠ 0 : minkowskiSquare p = 0}]   (LIGHT-FORM)
           ∨  [0 ∈ acc(support)]                                   (VERTEX-ACCUMULATION)
```

*Proof.* If `m*(T) = 0`, pick `pₙ ∈ supp E⊥` with `√(p²(pₙ)) < 1/n`. If
{pₙ} is bounded, a subsequence converges to `p* ∈ supp` (support closed) with
`p*² = 0`; by Lemma 2.1 the vertex has no atom on Ω⊥, but the vertex may be a
limit point — that is exactly the second disjunct when `p* = 0` and the first
when `p* ≠ 0`. If {pₙ} is unbounded with `p²(pₙ) → 0`, each pₙ is timelike
(on `forwardCone`, `p² = 0` only on the light cone, handled above), and its
boost orbit contains the rest point `(√(p²(pₙ)), 0)`, which lies in the
support by invariance; these rest points converge to the vertex. ∎

The converse is immediate. Consequently Part I's scenarios organize as:

| Primitive mechanism | Part I scenarios | Sub-division (independent since measure-theoretic) |
|---|---|---|
| LIGHT-FORM | A1 | atomic shell weight vs. non-atomic support asymptotic to the cone at finite or unbounded energy; **massless with momentum ≥ c is a legal sub-case** (its boost orbit is closed, cone-invariant, and misses the vertex) |
| VERTEX-ACCUMULATION | A2, A3 | atomic towers `p²ₙ ↓ 0` (A2) vs. non-atomic support reaching `s = 0` (A3a finite-order density, A3b infinite-order flat) |

Scenario cells that are **not** failures — and are routinely confused with them
— must be recorded to make the lattice complete:

| Cell | Spectral signature | Gap status |
|---|---|---|
| Infraparticle | non-atomic support in `{p² ≥ μ²}`, `μ > 0`, no mass shell | **gap-compatible** (no violation; only the pole/LSZ picture fails) |
| Threshold continua | support in `{p² ≥ n·m₁}` | gap-compatible; thresholds never undercut the one-particle gap (C5) |
| Wigner continuous-spin | support on the light cone only | light-form; excluded by C2 like any massless sector; multiplicity handled by matrix-valued (polarized) measures |
| Metastable/tunneling pair | finite-volume gap `λ(V) ~ e^{−σV}` | **thermodynamic-limit gap stays positive**; the finite-volume *rate* collapse is benign, unlike zero-mode collapse `λ(V) ~ V^{−α}` which is the A1/A2 mechanism |
| Hydrodynamic/diffusive low modes | `p⁰ ~ D‖p⇗‖²` near the vertex | violates the gap iff present; in the vacuum sector this is precisely what C2 + C1 must exclude |

Together with the architectural scenarios (A4 character dilution, A5
subsequence/selection multiplicity, A6 triviality, A7 degeneracy — already
excluded by `W0.uniqueVacuum` for a fixed constructed theory), this exhausts
the possibilities: a Wightman theory in the sense of the repository fails to
have a mass gap in no way other than (LIGHT-FORM ∨ VERTEX-ACCUMULATION), possibly
generated by the selection architecture rather than by any single phase.

## 9. The per-character refinement

The detailed theorem makes Part I's A4 analysis concrete:
`YM.Nonperturbative.Headline.Reconstruction` contains

```
characters (i : F.α.space.X) : WightmanAxioms (L.actors i) (L.contours i).world
average (n) (v) (g) : ∫ i, (L.contours i).world.W n v g ∂F.α.space.μ = F.B.world.W n v g
```

so **every** character `i` carries a full Wightman theory — including the
spectrum condition (`spectral`, `forward`) and vacuum uniqueness (`unique`) —
and the unselected boundary distributions are exactly the character-average of
the per-character moments. Therefore:

- **Definition.** `m(χ) := sup { m : MassGap(L.actors χ THEORY, m) }` for each
  `χ : Character` (each actor has its own PVM).
- **Fact (one-line measure argument).** The unselected (Wilson-limit)
  correlations decay exponentially with rate `m` iff `m(χ) ≥ m` for
  `μ_phase`-a.e. `χ`: the average of an exponential tail of rate `m` and any
  slower tail is the slower tail. With `fullSupport`, a *gapless character of
  positive measure* (or of any adherence in the support, via
  `characterContinuity`) poisons the unselected limit even if `selected` is
  massive.
- **Lemma 5.3 upgrade.** Since every `L.actors χ` has its own spectrum
  condition and unique vacuum, Theorem 5.1 applies *per character*: `MassGap`
  for the selected phase is strictly a statement about the single point
  `selected`; uniformity across `χ` (compactness + l.s.c. of `χ ↦ m(χ)`, or
  direct per-character estimates) is required **only** for a gap statement
  about the `none` phase, about the leading Wilson limits, or for robustness
  of the selection (A5).

## 10. The exclusion inventory and the quantifier audit

Why no proved statement discriminates the scenarios — stated as a quantifier
audit; this is the formal version of Part I's §3.3 proposition, and it covers
the detailed theorem's extra conclusions as well.

| Proved input | Quantifiers | What it sees |
|---|---|---|
| `WilsonRegularity` | fixed finite stencil; all spacings and volumes; UV slope | local/UV only |
| `Reconstructed` (`W0`–`W3`, mixture, continuation) | algebraic identities + support of spectral measures in the cone; **no lower bound away from the cone's vertex** | consistent with all of A1–A3, A4, A5 |
| `SeparatedOPE` / `NestedOPE` | `r → 0`, uniform on compact separated clusters, in every character and for `none` | short distance only; IR-blind |
| `TraceTest` (`shortDistance`, `excludes`) | `r → 0`; finite mass-shell Wick sums | UV; kills the finite/free part of A6 (trace channel) |
| `TraceExclusions` (`wick`, `maxwell`, `invariant`) | probe-based, finite tests | kills finite Wick palettes, Maxwell Fock and invariant-sector realizations of the trace signal — all *representational* exclusions; an **interacting** massless spectrum (A1 proper), towers (A2) and continua (A3) are untouched |
| Contacts / `MultipleLight` / `Position.FourMeters` | coincidence configurations, leading tests | UV again |

**Corollary (blind-spot; strengthens Part I §3.3).** No proved input for this
construction makes any statement about the spectral measure of `E⊥` on the
union of any neighbourhood of the vertex with any neighbourhood of the light
cone within `forwardCone`. Both primitive mechanisms of Theorem 8.1 therefore
survive every proved conclusion, and the conditions C1/C2 of Part I are not
only sufficient — modulo Theorem 5.1 — but *logically unsourced* from the
current theorem: new analytic input is unavoidable.

## 11. The gap, formulated eight ways at once

For fixed `m > 0`, the following are equivalent (or one-sided certificates as
marked); this is the simultaneous picture of where the gap can be *tested*:

| # | Formulation | Level | Note |
|---|---|---|---|
| G1 | `E⊥(LowRegion m) = 0` (definition, §2) | A | the target |
| G2 | tested supports: `E⊥` vanishes on a countable base of `LowRegion m` | A | `YM/Spectral/Frequencies.lean` machinery |
| G3 | `E⊥` timelike-spectrum `≥ m` **and** no light-form (Theorem 5.1) | A | the splitting: energy gap ⊕ masslessness |
| G4 | uniform temporal Laplace clustering on the word-generating dense set (Theorem 5.2) | A | certificate form of G3's first half |
| G5 | `‖E t − E₀‖_{Ω⊥} ≤ e^{−mt}` for the reflection-positive semigroup; `ground = ℂΩ` | A | `YM/OS`; the natural computational home |
| G6 | spatial exponential clustering with rate `m` for every label's stationary two-point | B(needed: fiber strip) | **necessary only**; fails to see light-form-with-momentum-cutoff (Fact 4.2.2); use as a check, not as a certificate |
| G7 | zero-momentum-projected temporal two-point rates `≥ m` uniformly over labels/towers | A− | needs the word-state lift (C3); equivalent to G4 pointwise |
| G8 | finite-volume transfer gaps `λ(V) ≥ λ₀ > 0` along *every* volume refinement, inherited by the reconstruction | C | the lattice-side route; fails benignly under tunneling, badly under zero modes |
| G9 | resolvent form: `self-adjoint evaluation ‖(P⁰+z)⁻¹|_{Ω⊥}‖ ≤ 1/(m+z)` for all (equivalently one) `z > 0` via the diagonal measures | A | spectral-evaluation identity; tunable certificate |
| G10 | Dirichlet/Cheeger form: a nontrivial Cheeger constant `h > 0` for the reflection-positive conductance gives gap `≥ h²/2` | B (sufficient only) | the lattice-analysable route; isoperimetry converted into IRG |

The equivalence chain G1 ⟺ G2 ⟺ G3 ⟺ G4 ⟺ G5 is the rigorous core
(functional analysis + the proved `W0`–`W3`); G6/G8 are the physically
favored external evidence routes and demand the Level-[C] input.

## 12. The minimal additional input, stated exactly

**Postulate IRG(m) (uniform infrared gap).** There is `m > 0` and, for each
character `χ`, a finite constant `C_χ` such that for every word state
`ψ ⊥ Ω_χ` of `L.actors χ`:

```
∫ e^{−τ p⁰} dμ^{(χ)}_ψ ≤ C_χ e^{−mτ}   for all τ ≥ 0.
```

**Postulate NL (no light-form).** For the selected phase,
`E⊥({p ≠ 0 : minkowskiSquare p = 0}) = 0`.

**Theorem 12.1 (conditional mass gap; assembles Part I §2, §5 and Part II §8).**
`JointExistence` (or `WilsonExistence`) + IRG(m) + NL ⟹ `MassGap(T, m)` for
the reconstructed selected phase; the three independent inputs are
best-possible in the sense of §10 (removing any one admits a model consistent
with all proved data: drop NL — light-form with momentum cutoff; drop IRG — A2
tower or A3 continuum; drop the joint occurrence — A4/A5 through the
selection). Conversely `MassGap(T, m)` ⟹ IRG(m) + NL with the same `m`.

Hence the conditions for a mass gap, in final form:

1. **Energy gap** (IRG, equivalently G3/G4/G5) — the dynamical core.
2. **No light-form** (NL) — masslessness exclusion, confinement-side.
3. **Uniformity**: across states (word-lift, C3 — free), across characters
   (only if the `none` limits or selection robustness are claimed), and across
   volume refinements (A5; either selection stability or a `∀`-refinement
   version of IRG).

**Open status, stated sharply.** IRG and NL are exactly the two statements
about `E⊥` on the vertex- and light-neighbourhoods that the construction does
not constrain (§10). Routes: (R1) prove `λ(V) ≥ λ₀` with the zero-mode
control that excludes `λ(V) → 0` (G8); (R2) reflection-positive semigroup
estimates in `YM/OS`/`YM/Heat` yielding G5 directly; (R3) a Tauberian/OPE
bridge upgrading the all-orders short-distance cascade to an infrared bound —
no known mechanism, listed for completeness; (R4) physical input: positivity of
the string tension plus a glueball argument (not yet a theorem in this
framework). NL additionally requires the absence of magnetic/Coulomb-sector
low modes — for pure Yang–Mills the expected confining answer, but no tool in
the repository computes it.

## 13. Part II summary

- The catalogue of Part I reduces, under `W2`-covariance, to **two primitive
  mechanisms** (light-form, vertex-accumulation), each with measure-level
  sub-cases; the commonly confused gap-compatible cells (infraparticles,
  thresholds, continuous spin, finite-volume tunneling) are separate and
  harmless cells of the lattice.
- The per-character Wightman theories proved in the detailed theorem turn
  A4/A5 into precise uniformity conditions rather than unreachable scenarios.
- The exclusion inventory is UV- and representation-bounded by quantifier
  audit: the proved data are silent exactly on the two primitive mechanisms.
- The gap equals IRG ∧ NL (Theorem 12.1), and every equivalent formulation
  (G1–G8) of it is now visible simultaneously, with its rigour level and its
  proof route.

---

# PART III — third pass: infrastructure, calculators, models, and the final conditions

## 14. The infrastructure map (what actually exists in the repository)

Direct reading of the modules that a gap proof must run through. This map
replaces generic scaffolding: every item below is a concrete object in this
repository.

| Module | Object produced | Role in the gap program |
|---|---|---|
| `YM/OS/Dynamics.lean` | **existence of the coordinate OS semigroups, unconditional from the Table hierarchy** | the G5 semigroup exists already; header anticipates "PVM work or analytic-vector approaches to rotation" |
| `YM/OS/Core.lean` | `Semigroup E t`, invariant subspace `ground := ⨅ t, ker(E t − id)` | G5's base eigenvalue; the gap statement is a norm statement on the orthocomplement of `ground` |
| `YM/OS/Flow.lean` | heat operators on the GNS spaces for non-temporal axes | spatial-direction analogues needed to compare G6 with G5 |
| `YM/OS/Train.lean`, `Halves.lean`, `Caps.lean`, `Slabs.lean` | train bounds with integral steps, slab operators over a range of widths | uniform-in-width cluster/slab estimates — raw material for spatial bounds |
| `YM/Heat/Lift.lean`, `Rows.lean` | continuous calculus on the bounded first-step, positive powers | lifting of heat bounds to general durations |
| `YM/Heat/Duration.lean` | **exact damping of spectral measures**: `descent t = e^{−t·p·a}`, `transform t μ = μ.withDensity (descent t)`, laws `stays_put`, `growth`, undamping operation | the Laplace/damping calculus already written on spectral measures — home of G4/G7/G9 |
| `YM/EveryPhase/Light.lean` | `lowE u := time⁻¹' Ioc 0 u`; character-function averaging with `oddTest` integrals | the low-energy slabs — exactly the sets in NL/IRG |
| `YM/EveryPhase/Projection.lean` | `aboveE`, `boltz s p = e^{−s·time p}` | Boltzmann weighting of spectral measures |
| `YM/EveryPhase/Decay.lean` | **theorem `decay`: `μ(lowE u) ≤ C·u² ⟹ ∫ boltz s dμ ≤ C·Γ(3)·s⁻²`** | quadratic-vertex-weight ⟹ heat-integral bound — the finite-order half of the IRG calculus, already proved |
| `YM/EveryPhase/Frequency.lean` | compact-frequency Schwartz tests recover "very hot" OS vectors via the full spectrum support; no analytic-vector density assumption | the analytic-vector bridge for the rotation/semigroup link in G5 |
| `YM/EveryPhase/Strip.lean`, `Average.lean` | strip derivatives; time-averaged vacuum commutators without uniform bounds | spectral-integral techniques available off the shelf |
| `YM/SNAG/Escape.lean` (with `Unital`, `Kernels`, `Approx`, `Dense`) | **"Full SNAG achieved … without assuming as a theorem"** | Bochner/Stone bridge: continuity ⟹ spectral representation; supports G4 without external spectral theorems |
| `YM/TraceExtension/LaplaceDensity.lean`, `LaplaceLimit.lean` | nonnegative-moment Tauberian, part I (tests separate compactified cone points); continuity theorem for the Laplace transform on the open future cone — Hausdorff-moment-style Tauberian for *positive* measures with "actual test-function implications" | the general positive-measure Laplace layer for turning Laplace-side hypotheses into spectral/test conclusions |
| `YM/TraceExtension/LogScaling.lean` | **Tauberian theorem on the log scale**: `EuclideanAsymptotic F A ⟹` spectral conclusions (`relative_limit`, `joint_limit`), anchored at `Zlog r = r⁻⁸·(log r)²` | a working model of exactly the wanted asymptotic⟹spectrum implication — but UV/trace-anchored |
| `YM/Pressure/` | pressure/free-energy computations with volume receipts | the thermodynamic side feeding G8 |
| `YM/Ground/` | generator slot in the character algebra; multi-cluster train limits; moment/permutation structure | per-character dynamics — feeds the gap function `m(χ)` of §9 |
| `YM/Spectral/Projection.lean`, `Frequencies.lean` | PVM interface and tested-support criteria | G2 directly |

Two conclusions from the map: (i) the *calculus* of the certificate chain
G2↔G3↔G4↔G7↔G9 is essentially complete in-repo (SNAG, measure damping,
low-slab tests, Laplace Tauberian for positive measures); (ii) what is **not**
in the repository is any *dynamical* input: no zero-mode/volume analysis, no
Cheeger/isoperimetry layer, no string tension, and the one existing
asymptotic→spectrum Tauberian is anchored at the UV cascade, not at the vertex.

## 15. The damped-measure calculus, made explicit

Combine `Heat/Duration` + `EveryPhase/Light` + `EveryPhase/Decay` into the
exact statements the gap program needs, all on *positive* measures on the
future cone (the public `EnergyMomentumMeasure.diagonal` measures qualify via
`diagonalIdentity` and `W0.positiveEnergy`).

**Lemma 15.1 (vertex nullity from pointwise Laplace decay). [A]**
If `∫ e^{−τp⁰} dμ ≤ C e^{−mτ}` for all `τ ≥ 0` and if `u < m`, then
`μ(lowE u) = 0`: on `lowE u` the integrand dominates `e^{−τu}·1`, so
`μ(lowE u) ≤ C e^{−τ(m−u)} → 0`. Since the region `{p : 0 ≤ time p < m}`
is the countable union of `lowE(m − 1/n)`-slabs (use `countablyAdditive`
of the PVM), this gives the timelike half of G3 from G4.

**Lemma 15.2 (the two equivalent certificate forms). [A]**
The *pointwise* form of IRG is G4; after one integration step it yields the
*integrated* form `∫ boltz s dμ_ψ ≤ C′ e^{−ms}`, which is what the semigroup
route (G5) naturally produces. In the reverse direction the proved
`EveryPhase.decay` lemma shows the best *finite-order* conclusion available
from a quadratic low-weight bound is polynomial (`s⁻²`), never exponential —
so the two forms coincide exactly at exponential precision, and Lemma 15.1
ties them with no Tauberian input. The Tauberian layer (`LogScaling`,
`LaplaceLimit`) is needed only when the hypothesis is itself an *asymptotic*
rather than a bound; adapting it from the `Zlog` UV anchor to a vertex anchor
is build item N5 (§18).

## 16. Model audit — sharpness and independence of IRG / NL

Each model specifies spectral/PVM-support structure on the closed forward
cone. The audit checks Theorem 12.1 cell by cell:

| Model | Spectral structure | IRG | NL | Mass gap | Verdict vs. 12.1 |
|---|---|---|---|---|---|
| M1 free massive scalar | shell at `s = m²` | ✓ | ✓ | ✓ | consistent |
| M2 free massless scalar | cone shell `s = 0`, reaching the vertex | ✗ | ✗ | ✗ | consistent |
| M3 massless with momentum cutoff `‖p⇗‖ ≥ c` | `{p⁰ = ‖p⇗‖ ≥ c}`, closed, invariant, misses the vertex | **✓** | **✗** | ✗ | **NL necessary even under IRG** |
| M4 atomic tower masses `mₙ = 2⁻ⁿ` | atoms at rest points, `p²ₙ ↓ 0` | **✗** | ✓ | ✗ | **IRG necessary even under NL** |
| M5 vertex continuum `ρ(s) = e^{−1/s}` | non-atomic at the vertex, super-algebraically flat | ✗ | ✓ | ✗ | same as M4 with a benign-looking continuum |

M3 confirms the legality claim of §8 at support level (its support is closed
and Poincaré-invariant, so W0-level scrutiny alone does not exclude it; whether
full `W0`–`W3`, locality and the reconstruction package admit such a theory is
not decided here — the audit certifies only that dropping NL *removes the
contradiction with the proved support-level data*). M5 reconfirms Fact 4.2.2:
flatness to infinite order does not restore a rate. Overall Theorem 12.1 is
exact: IRG ∧ NL is both necessary and sufficient, and neither postulate is
redundant.

## 17. Toolbox constraints — what cannot be assumed

| Tool | Status for this problem | Consequence |
|---|---|---|
| FKG / attractivity / monotone comparison | unavailable: the Yang–Mills measure is not monotone; Ginibre inequalities do not apply to the plaquette action | no uniqueness-by-domination shortcuts; the reflection-positive semigroup route carries the rigorous side |
| Cluster / polymer expansions | strong coupling only, while the constructed families sit in the asymptotically-free regime (positive running slope `2·b₀`) | cannot import weak-coupling/massless-screening analysis wholesale |
| Transfer matrices (Kogut–Susskind, Lüscher) | exist in the literature; the repository's `YM.OS` semigroups are the analogous already-proved objects on the Euclidean side | route R1/R2 is buildable in-repo rather than external |
| Cheeger / Dirichlet-form inequalities | absent from the repository; finite-volume Markov generators are finite-dimensional | G10 is a feasible new module, but the required isoperimetric constant is the actual physics |
| Constructive IR renormalisation-group flow | the repository carries the all-orders OPE cascade but no IR flow bound | R3 has no known carrier; listed for completeness |
| Seiberg–Witten-type exact results | different theory class | analogy only; no transferable mechanism |

## 18. Build items, ordered by leverage

1. **N1 — `MassGap.lean` core [A]:** `LowRegion`, `MassGap`, Lemma 2.1; then
   the translation half of Theorem 5.1 (timelike support from energy gap) via
   Lemma 15.1 on the `diagonal` measures. Uses only public signatures.
2. **N2 — Theorem 5.2 [A]:** uniform temporal Laplace clustering ↔ the energy
   half of G3, lifted from the word-generating dense set by `W1` plus
   continuity/countable additivity of the projections.
3. **N3 — backbone chain G1↔G2↔G3↔G4↔G5↔G9 [A]:** tested supports
   (`Spectral.Frequencies`), the semigroup norm statement on the orthocomplement
   of `ground` (`OS/Core`), resolvent evaluation; SNAG handles the
   character-function bookkeeping.
4. **N4 — per-character lift [A]:** from `Headline.Reconstruction.characters`
   to per-character PVMs and the gap function `m(χ)`; Lemma 5.3 uniformity
   under lower semicontinuity; closes the C4 clause.
5. **N5 — vertex-anchored Tauberian [B]:** re-derive the `LogScaling`
   architecture with the anchor at the `lowE` slabs: hypotheses = scaling
   regimes of the zero-mode temporal two-point at large times; conclusions =
   lower semicontinuity/positivity of the spectral edge. Turns any future
   *asymptotic* infrared estimate into IRG automatically — the single
   highest-leverage new module.
6. **N6 — finite-volume descend [C — the dynamical core]:** from
   `λ(V) ≥ λ₀` uniform over all volume refinements (G8) plus reconstruction
   compatibility, to IRG(`λ₀`). Requires the zero-mode control distinguishing
   benign tunneling (`e^{−σV}`) from A1/A2 collapse (`V^{−α}`); nothing in the
   repository performs this step.
7. **N7 — NL test [A given NL; C to prove NL]:** light-form exclusion as a
   countable family of projection tests (G2 style) in the selected phase.

## 19. The conditions, final form

Assembling Parts I–III, the entire approach arrives at:

**Exact characterisation (Theorem 12.1, audited in §16):**

```
MassGap(T, m)   ⟺   IRG(T, m)   ∧   NL(T)
```

where IRG ⟺ G4 ⟺ G5 ⟺ G9 is the energy gap with a free uniformity lift
across states (density, C3), and NL is the light-form exclusion. Uniformity
clauses:

- across **states**: free (word-state density from `W1`, continuity of
  projections) — no extra condition;
- across **characters**: conditional — required only for `none`-phase/leading
  Wilson-limit statements and for selection robustness (A4/A5); the
  per-character theories of `Headline.Reconstruction` make the statement
  well-formed;
- across **volume refinements**: the `∀`-refinement version of IRG feeds N6;
  if selection is unstable (A5) the theorem-level claim must hold for every
  refinable phase or be paired with selection stability.

**Certificate bundles (any one yields IRG):** G5 semigroup gap with
`ground = ℂΩ`; G8-uniform finite-volume gaps with zero-mode control; G10 Cheeger/isoperimetry; a vertex-anchored Tauberian (N5) applied to asymptotic
infrared estimates of the zero-mode temporal two-point at all orders.

**Negative results (honesty of the condition list):** no mass gap follows from
the proved data alone (§10 quantifier audit — every scenario cell survives);
spatial exponential clustering is only *necessary* (Fact 4.2.2, model M3);
spectral flatness buys nothing (M5); finite-volume gap collapse alone
diagnoses nothing (tunneling vs zero-mode, §8).

## 20. Summary of the three passes

1. **Part I** fixed the target in the public language, catalogued every
   failure mechanism, developed the rate calculus, and stated the first
   condition list C1–C5.
2. **Part II** reduced the catalogue, under `W2`-covariance, to two primitive
   mechanisms (light-form, vertex-accumulation), recorded the gap-compatible
   cells, upgraded the per-character picture from the detailed theorem,
   audited the proved inputs by quantifier, and stated the minimal input
   IRG ∧ NL (Theorem 12.1).
3. **Part III** mapped the real infrastructure (OS semigroups, spectral
   damping, low-energy slabs, SNAG, Laplace and log-scale Tauberians, pressure
   receipts), proved-style the elementary bridges (Lemma 15.1/15.2) that make
   G2↔G3↔G4↔G9 rigorous with no new spectral theory, audited the toolbox,
   enumerated the build items N1–N7, and consolidated the final conditions
   with a model audit showing IRG and NL are both necessary and jointly
   sufficient.

The remaining problem is precisely N6 (with N7): a uniform infrared energy
gap and the absence of lightlike spectral weight for the constructed phases.
Everything else in the chain is proved or buildable from existing repository
infrastructure.
