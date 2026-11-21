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
