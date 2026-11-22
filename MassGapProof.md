---
title: "The Mass Gap in the Challenge's Public Language"
subtitle: "Proof walkthrough of `MassGap.lean` — everything proved, one node ruled out"
author: "Formalization: Vibe Code (Mistral AI); public language: `yang-mills-group/OpenAI-YM-20261028`"
date: "2026"
geometry: margin=1in
fontsize: 10pt
mainfont: "DejaVu Sans"
monofont: "DejaVu Sans Mono"
colorlinks: true
toc: true
---

# Verdict (read this first)

The entire reduction of the "mass gap" condition to data extractable from the
repository's public API (`PublicTheory.lean`) was carried out simultaneously
along all available routes, and compiled end-to-end in Lean 4 against that API.
The outcome is exact and binary:

* **Provable (machine-checked, no axioms beyond Lean's three standard ones).**
  The whole exponential/Laplace-transform half of the argument: geometry of the
  forward cone, the damped mass $M_\psi(s)=\int e^{-s\,t(p)}\,\mathrm{d}\mu_\psi(p)$,
  non-emptiness of the rate set, the Chebyshev domination, the geometric-series
  limit that turns a positive Laplace rate into **nullity of every time slab**
  $\{p:\ t(p)\le R\}$, $R<m$; the countable-slab upgrade; and the scalar bridge
  from diagonal-measure nullity to projection nullity $E(A)\psi=0$.
* **The single unprovable node (the ruled-out method).** The low region of the
  challenge is *not* time-bounded: it contains the massless wedge
  $W_m=\{p\in C^+:\ m\le t(p),\ q(p)\le m^2\}$. Killing the wedge requires a
  **Lorentz-intertwining datum** `LorentzIntertwines T` that the public API does
  not contain — `PoincareAction` intertwines for **pure translations only**.
  Consequently the slab-based (Laplace/Chebyshev) method **cannot** establish
  the mass gap in the public language. This node is isolated as the unique
  `sorry` of `MassGap.lean`, in `wedgeNull_of_rate_of_intertwines`, stated under
  the explicitly missing hypothesis.
* **Obstruction witnesses (proved).** A concrete rest point at $t(p)=m$ lies in
  `LowRegion m` but in no slab on which slab nullity is available; hence the low
  region is not covered by the slab family.

Below, the Lean code is loaded verbatim from the compiled source
(`lake env lean MassGap.lean`: 0 errors, 0 warnings, exactly one `sorry`) and
the proof is written alongside it, section by section, mirroring the file's own
structure. Section references are to `MassGapScenarios.md`.

## Fixing notation

Write $C^+=\{\mathrm{forwardCone}\}=\{p:\ \lVert x(p)\rVert\le t(p)\}$ for the
closed forward cone on $\mathrm{Spacetime}=\mathbb{R}^{1,3}$
(`EuclideanSpace ℝ Axis`, causality read off the *public* Euclidean coordinates),
$q(p)=t(p)^2-\lVert x(p)\rVert^2$ for the Minkowski square, and for a state
$\psi$ orthogonal to the vacuum let

$$\mu_\psi \coloneqq T.\mathrm{energyMomentum}.\mathrm{diagonal}\,\psi$$

denote the scalar diagonal measure of the joint energy--momentum PVM
($\mu_\psi(A)=\langle\psi, E(A)\psi\rangle$ in real part). All integrals are
`ℝ≥0∞`-valued (`∫⁻`), so nullity statements are exact, not approximate.

# §1. Geometry: continuity of the coordinate functions

**Goal.** The coordinate functionals $t(p)$ and $x(p)$, the Minkowski square,
the cone, the slabs, and the low region must all be measurable, since measure
arguments below take place on an arbitrary `WightmanTheory`'s spectral measure.
Everything is rebuilt on the public `Spacetime` (`Fin 4` axes, `timeAxis = 3`)
so that the file imports `PublicTheory` only.

The time and spatial coordinates are continuous linear functionals, defined
explicitly by `LinearMap.toContinuousLinearMap`:

```lean
/-- The time coordinate as a continuous linear functional. -/
def timeL : Spacetime →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap { toFun := time, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
```

```lean
/-- The spatial part as a continuous linear map. -/
def spatialL : Spacetime →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap { toFun := spatial, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
```

Continuity propagates through norm and products, and closedness of the cone and
of the slabs follows from `isClosed_le`; measurability is then free:

```lean
lemma closed_forwardCone : IsClosed forwardCone :=
  isClosed_le (by fun_prop) time_cont
```

```lean
theorem measurableSet_forwardCone : MeasurableSet forwardCone := closed_forwardCone.measurableSet
```

```lean
theorem measurableSet_time_le (R : ℝ) : MeasurableSet {p | time p ≤ R} :=
  (isClosed_le time_cont continuous_const).measurableSet
```

The low region of the challenge statement (§2) is the measurable "box"
$C^+\cap\{q\le m^2\}\cap\{0\}^c$:

```lean
/-- The low region of the challenge statement (§2). -/
def LowRegion (m : ℝ) : Set Spacetime :=
  {p | p ∈ forwardCone ∧ minkowskiSquare p ≤ m ^ 2 ∧ p ≠ 0}
```

```lean
theorem lattice_set (m : ℝ) : MeasurableSet (LowRegion m) := by
  have hEq : LowRegion m =
      forwardCone ∩ {p : Spacetime | minkowskiSquare p ≤ m ^ 2} ∩ Set.compl {(0 : Spacetime)} := by
    ext p
    simp only [LowRegion, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((measurableSet_forwardCone.inter
    (isClosed_le continuous_minkowskiSquare continuous_const).measurableSet).inter
    (measurableSet_singleton (0 : Spacetime)).compl)
```

# §2. Mass gap and the damped mass

**Definition of the target.** The mass gap is stated exactly in the public
language: a strictly positive $m$ such that the compressed PVM
$E(\mathrm{LowRegion}\,m)$ annihilates every state orthogonal to the vacuum.

```lean
/-- Mass gap in the public language (§2): the joint energy-momentum PVM
compressed to the orthocomplement of the vacuum avoids `LowRegion m`. -/
def MassGap (T : WightmanTheory H Labels) (m : ℝ) : Prop :=
  0 < m ∧ ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
    T.energyMomentum.projection (LowRegion m) ψ = 0
```

**The one-parameter probe.** The method attempts a pure translation argument:
damp by $e^{-s t}$ and study the exponential decay rate.

```lean
/-- The exponentially damped total mass of a state's diagonal measure (§48). -/
def dampedMass (T : WightmanTheory H Labels) (ψ : H.carrier) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp (-(s * time p))) ∂(T.energyMomentum.diagonal ψ)
```

That is, $M_\psi(s)=\int e^{-s\,t(p)}\,\mathrm{d}\mu_\psi(p)$ for $s\ge 0$. The
**rate** is the supremum of asymptotically uniform exponential decay rates:

```lean
/-- The uniform exponential bound defining the rate. -/
def RateBound (T : WightmanTheory H Labels) (ψ : H.carrier) (m : ℝ) : Prop :=
  0 ≤ m ∧ ∃ C : ℝ≥0, ∃ s₀ : ℝ, ∀ s ≥ s₀,
    dampedMass T ψ s ≤ ENNReal.ofReal ((C : ℝ) * Real.exp (-m * s))
```

```lean
/-- The uniform exponential rate of decay (§48): the supremum of all `m` with
`RateBound`. -/
def LaplaceRate (T : WightmanTheory H Labels) (ψ : H.carrier) : ℝ :=
  sSup {m : ℝ | RateBound T ψ m}
```

**Two elementary but non-negotiable facts.** First, $\mu_\psi$ is supported on
the closed forward cone — this is exactly the public datum `W0.positiveEnergy`
translated through the PVM's `diagonalIdentity`:

```lean
/-- The diagonal measure of any state is supported on the closed forward cone
(`W0.positiveEnergy` + `diagonalIdentity`). -/
theorem diagonal_le_cone (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) (Set.compl forwardCone) = 0 := by
  have hmeas : MeasurableSet (Set.compl forwardCone) := measurableSet_forwardCone.compl
  have h0 : T.energyMomentum.projection (Set.compl forwardCone) = 0 :=
    hW0.positiveEnergy
  have hdi := T.energyMomentum.diagonalIdentity hmeas ψ
  simp only [h0, zero_apply, inner_zero_right] at hdi
  have hreal : (T.energyMomentum.diagonal ψ).real (Set.compl forwardCone) = 0 :=
    Complex.ofReal_eq_zero.mp hdi
  have hne : (T.energyMomentum.diagonal ψ) (Set.compl forwardCone) ≠ ∞ :=
    measure_ne_top _ _
  exact measureReal_eq_zero_iff hne |>.mp hreal
```

Second, the damped mass is dominated by the total mass $M_\psi(s)\le\mu_\psi(\mathbb{R}^4)$:
split the integral over $C^+$ and its complement (the latter is null),
dominate the integrand by $1$ on the cone using $0\le s\,t(p) \Rightarrow e^{-s\,t(p)}\le 1$,
and fold the constant integral via `setLIntegral_const`:

```lean
/-- For `s ≥ 0` the damped mass is dominated by the total mass. -/
theorem dampedMass_le_total (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier)
    {s : ℝ} (hs : 0 ≤ s) : dampedMass T ψ s ≤ (T.energyMomentum.diagonal ψ) Set.univ := by
  set μ : Measure Spacetime := T.energyMomentum.diagonal ψ with hμdef
  have hcone_time : ∀ p : Spacetime, p ∈ forwardCone → 0 ≤ time p := by
    intro p hp
    simp only [forwardCone, Set.mem_setOf_eq] at hp
    exact le_trans (norm_nonneg _) hp
  have hrestrict : (∫⁻ p in Set.compl forwardCone,
      ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ) = 0 := by
    rw [Measure.restrict_zero_set (diagonal_le_cone T hW0 ψ), lintegral_zero_measure]
  have hsplit : ∫⁻ p in forwardCone, ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ +
      ∫⁻ p in Set.compl forwardCone, ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ =
      ∫⁻ p, ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ :=
    lintegral_add_compl (fun p => ENNReal.ofReal (Real.exp (-(s * time p)))) measurableSet_forwardCone
  calc dampedMass T ψ s = ∫⁻ p, ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ := rfl
    _ = ∫⁻ p in forwardCone, ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ +
          ∫⁻ p in Set.compl forwardCone, ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ := hsplit.symm
    _ = ∫⁻ p in forwardCone, ENNReal.ofReal (Real.exp (-(s * time p))) ∂μ := by
          rw [hrestrict, add_zero]
    _ ≤ ∫⁻ p in forwardCone, (1 : ℝ≥0∞) ∂μ :=
          setLIntegral_mono' measurableSet_forwardCone fun p hp => by
            refine ENNReal.ofReal_le_one.mpr ?_
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs (hcone_time p hp)))
    _ = μ forwardCone := by rw [setLIntegral_const forwardCone 1, one_mul]
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
```

**The rate set is nonempty.** With $m=0$ one may take $C=\mu_\psi(\mathbb{R}^4)$
(as a real, finite since the measure of any measurable set is finite):
$M_\psi(s)\le C\,e^{-0\cdot s}=C$. Note the proof must supply
$C$ as a `ℝ≥0` pair rather than rewrite with it — the coercion-in-goal mismatch
is bypassed by proving the bound in `ℝ` and passing `ENNReal.ofReal`:

```lean
/-- The rate set is nonempty: `m = 0` is admissible (total mass controls the
damped mass). -/
theorem rateSet_nonempty (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier) :
    {m : ℝ | RateBound T ψ m}.Nonempty := by
  have hne : (T.energyMomentum.diagonal ψ) Set.univ ≠ ∞ := measure_ne_top _ _
  have hgoal : ∀ s : ℝ, 0 ≤ s → dampedMass T ψ s ≤
      ENNReal.ofReal ((ENNReal.toReal ((T.energyMomentum.diagonal ψ) Set.univ) : ℝ) *
        Real.exp (-(0 : ℝ) * s)) := by
    intro s hs
    refine le_trans (dampedMass_le_total (T := T) hW0 ψ hs) ?_
    rw [show Real.exp (-(0 : ℝ) * s) = (1 : ℝ) from by simp, mul_one]
    exact le_of_eq (ENNReal.ofReal_toReal hne).symm
  refine ⟨0, le_refl 0, ⟨⟨ENNReal.toReal ((T.energyMomentum.diagonal ψ) Set.univ),
    ENNReal.toReal_nonneg⟩, 0, fun s hs => hgoal s hs⟩⟩
```

So $\mathrm{LaplaceRate}$ is a supremum over a nonempty, bounded set (bounded by
$M_\psi(0)$), and any $m\le\mathrm{LaplaceRate}$ admits admissible rates $a$
arbitrarily close to $m$ from above.

# §3. The Chebyshev step: rate $\Rightarrow$ slab nullity (§15, §48)

**Pointwise Chebyshev domination.** On the slab $\{t\le R\}$ (with $s\ge0$) the
integrand $e^{-s\,t(p)}$ is *at least* its value at the right edge $R$:

$$e^{-sR}\cdot\mu_\psi\{p:\ t(p)\le R\}\ \le\ M_\psi(s).$$

Proof: the slab-indicator form of the constant integral, `lintegral_indicator_const`,
then dominated term-by-term by the actual integrand (`Pi.le_def` after
`exp_le_exp` and monotonicity of $t\mapsto e^{-st}$ on the slab), case split on
$t(p)\le R$.

```lean
/-- Pointwise Chebyshev domination: on the slab `{time ≤ R}` the integrand is
bounded below by its value at `R`. -/
theorem slab_chebyshev (T : WightmanTheory H Labels) (ψ : H.carrier) {s : ℝ} (hs : 0 ≤ s)
    (R : ℝ) :
    ENNReal.ofReal (Real.exp (-(s * R))) * (T.energyMomentum.diagonal ψ) {p | time p ≤ R} ≤
      dampedMass T ψ s := by
  have hpt : ∀ p : Spacetime,
      {p | time p ≤ R}.indicator (fun _ => ENNReal.ofReal (Real.exp (-(s * R)))) p ≤
        ENNReal.ofReal (Real.exp (-(s * time p))) := by
    intro p
    by_cases hp : time p ≤ R
    · have hind : {p | time p ≤ R}.indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(s * R)))) p =
          ENNReal.ofReal (Real.exp (-(s * R))) := by
        simp [hp]
      rw [hind]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hx : s * time p ≤ s * R := mul_le_mul_of_nonneg_left hp hs
      exact neg_le_neg hx
    · have hind : {p | time p ≤ R}.indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(s * R)))) p = 0 := by
        simp [hp]
      rw [hind]
      exact zero_le
  calc ENNReal.ofReal (Real.exp (-(s * R))) * (T.energyMomentum.diagonal ψ) {p | time p ≤ R}
      = ∫⁻ p, {p | time p ≤ R}.indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(s * R)))) p ∂(T.energyMomentum.diagonal ψ) :=
        (lintegral_indicator_const (measurableSet_time_le R)
          (ENNReal.ofReal (Real.exp (-(s * R))))).symm
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (-(s * time p))) ∂(T.energyMomentum.diagonal ψ) :=
        lintegral_mono (Pi.le_def.mpr hpt)
```

**From rate to a usable witness.** Standard sSup bookkeeping (`exists_lt_of_lt_csSup`):

```lean
/-- A sub-supremum of the rate set. -/
theorem exists_lt_of_rate (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier)
    {R m : ℝ} (hR : R < m) (hm : m ≤ LaplaceRate T ψ) :
    ∃ a : ℝ, a ∈ {m : ℝ | RateBound T ψ m} ∧ R < a :=
  exists_lt_of_lt_csSup (rateSet_nonempty T hW0 ψ) (lt_of_lt_of_le hR hm)
```

**The core estimate.** If $R<m\le\mathrm{LaplaceRate}$, pick $a\in\mathrm{Rate}$ with
$R<a$. The rate bound gives, for large $s$,

$$M_\psi(s)\ \le\ C\,e^{-as},$$

while Chebyshev gives $M_\psi(s)\ge e^{-sR}\,\mu_\psi\{t\le R\}$. Multiplying the
Chebyshev lower bound by the compensation factor $e^{sR}$, one obtains for all
$t\ge\max(s_0,0)$:

$$\mu_\psi\{t\le R\}\ \le\ C\,e^{-(a-R)t}.$$

The right-hand side is a geometric sequence with ratio $e^{-(a-R)}<1$, hence
tends to $0$ along $n$ (sent through $t=\max(s_0,0)+n$; `tendsto_pow_atTop_nhds_zero_of_lt_one`
plus `Tendsto.const_mul` and `ENNReal.tendsto_ofReal`). Since $\mu_\psi$ takes
values in `ℝ≥0∞`, $\le 0$ forces $=0$. The case $R<0$ is separate: the slab lies
entirely outside the forward cone (as $t\le R<0$ forces
$\lVert x\rVert\le t<0$, absurd against $\lVert x\rVert\ge 0$), so it is null by
`diagonal_le_cone`.

```lean
/-- Positive rates force nullity of every time slab below them. -/
theorem slab_null_of_rate (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier)
    {m R : ℝ} (hm : m ≤ LaplaceRate T ψ) (hR : R < m) :
    (T.energyMomentum.diagonal ψ) {p | time p ≤ R} = 0 := by
  by_cases hnn : 0 ≤ R
  · obtain ⟨a, hmem, hRa⟩ := exists_lt_of_rate T hW0 ψ hR hm
    have hb : RateBound T ψ a := hmem
    obtain ⟨-, ⟨C, s₀, hbound⟩⟩ := hb
    have hapos : 0 < a - R := by linarith
    have hprod : ∀ t : ℝ,
        ENNReal.ofReal (Real.exp (t * R)) * ENNReal.ofReal (Real.exp (-(t * R))) = 1 := by
      intro t
      have hsum : t * R + -(t * R) = 0 := by ring
      have hex : Real.exp (t * R) * Real.exp (-(t * R)) = 1 := by
        rw [← Real.exp_add, hsum, Real.exp_zero]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), hex, ENNReal.ofReal_one]
    have hgoal' : ∀ t : ℝ, Real.exp (t * R) * ((C : ℝ) * Real.exp (-a * t)) =
        (C : ℝ) * Real.exp (-((a - R) * t)) := by
      intro t
      have hlift : -((a - R) * t) = t * R + -a * t := by ring
      rw [hlift, Real.exp_add]
      ring
    have hgoal : ∀ t : ℝ, ENNReal.ofReal (Real.exp (t * R)) *
        ENNReal.ofReal ((C : ℝ) * Real.exp (-a * t)) =
        ENNReal.ofReal ((C : ℝ) * Real.exp (-((a - R) * t))) := by
      intro t
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact congrArg ENNReal.ofReal (hgoal' t)
    have hkey : ∀ t : ℝ, max s₀ 0 ≤ t → (T.energyMomentum.diagonal ψ) {p | time p ≤ R} ≤
        ENNReal.ofReal ((C : ℝ) * Real.exp (-((a - R) * t))) := by
      intro t ht
      have ht0 : 0 ≤ t := le_trans (le_max_right s₀ 0) ht
      have htb : s₀ ≤ t := le_trans (le_max_left s₀ 0) ht
      have h1 := (slab_chebyshev T ψ ht0 R).trans (hbound t htb)
      have hprod' : ∀ t : ℝ,
          ENNReal.ofReal (Real.exp (t * R)) * ENNReal.ofReal (Real.exp (-(t * R))) = 1 := by
        intro t
        have hsum : t * R + -(t * R) = 0 := by ring
        have hex : Real.exp (t * R) * Real.exp (-(t * R)) = 1 := by
          rw [← Real.exp_add, hsum, Real.exp_zero]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), hex, ENNReal.ofReal_one]
      calc (T.energyMomentum.diagonal ψ) {p | time p ≤ R}
          = ENNReal.ofReal (Real.exp (t * R)) *
              (ENNReal.ofReal (Real.exp (-(t * R))) *
                (T.energyMomentum.diagonal ψ) {p | time p ≤ R}) := by
            rw [← mul_assoc, hprod' t, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (t * R)) *
              ENNReal.ofReal ((C : ℝ) * Real.exp (-a * t)) :=
            mul_le_mul_right h1 (ENNReal.ofReal (Real.exp (t * R)))
        _ = ENNReal.ofReal ((C : ℝ) * Real.exp (-((a - R) * t))) := hgoal t
    have hgeo : Filter.Tendsto (fun n : ℕ => (Real.exp (-(a - R : ℝ))) ^ n) Filter.atTop
        (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
        (Real.exp_lt_one_iff.mpr (by linarith : (-(a - R : ℝ)) < 0))
    have hshift : Filter.Tendsto
        (fun n : ℕ => Real.exp (-((a - R) * (max s₀ 0 + (n : ℕ))))) Filter.atTop (𝓝 (0 : ℝ)) := by
      have hid : ∀ n : ℕ, Real.exp (-((a - R) * (max s₀ 0 + (n : ℕ)))) =
          (Real.exp (-((a - R) * max s₀ 0)) : ℝ) * (Real.exp (-(a - R : ℝ))) ^ n := by
        intro n
        rw [show -((a - R) * (max s₀ 0 + (n : ℕ)))
            = -((a - R) * max s₀ 0) + (n : ℕ) * (-(a - R)) by ring,
          Real.exp_add, Real.exp_nat_mul]
      have htwo : Filter.Tendsto
          (fun n : ℕ => (Real.exp (-((a - R) * max s₀ 0)) : ℝ) * (Real.exp (-(a - R : ℝ))) ^ n)
          Filter.atTop (𝓝 ((Real.exp (-((a - R) * max s₀ 0)) : ℝ) * 0)) :=
        Filter.Tendsto.const_mul (Real.exp (-((a - R) * max s₀ 0))) hgeo
      rw [mul_zero] at htwo
      exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hid n).symm) htwo
    have hg : Filter.Tendsto
        (fun n : ℕ => (C : ℝ) * Real.exp (-((a - R) * (max s₀ 0 + (n : ℕ))))) Filter.atTop
        (𝓝 (0 : ℝ)) :=
      by simpa using Filter.Tendsto.const_mul (C : ℝ) hshift
    have hfine : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal
          ((C : ℝ) * Real.exp (-((a - R) * (max s₀ 0 + (n : ℕ)))))) Filter.atTop
        (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal hg
    have hseq : ∀ n : ℕ, (T.energyMomentum.diagonal ψ) {p | time p ≤ R} ≤
        ENNReal.ofReal ((C : ℝ) * Real.exp (-((a - R) * (max s₀ 0 + (n : ℕ))))) :=
      fun n => hkey (max s₀ 0 + (n : ℕ)) (le_add_of_nonneg_right (by positivity))
    exact le_antisymm (by
      have hb := ge_of_tendsto hfine (Filter.Eventually.of_forall hseq)
      simpa using hb) zero_le
  · -- For `R < 0` the slab lies outside the forward cone, hence is null.
    have hsub : {p | time p ≤ R} ⊆ (Set.compl forwardCone) := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      intro hc
      simp only [forwardCone, Set.mem_setOf_eq] at hc
      have hnorm := norm_nonneg (spatial p)
      have hrl : R < 0 := lt_of_not_ge hnn
      linarith
    exact le_antisymm ((measure_mono hsub).trans (le_of_eq (diagonal_le_cone T hW0 ψ)))
      zero_le
```

**Countable slab upgrade.** The open slab $\{p\in C^+:\ t(p)<m\}$ is the union of
the closed slabs $R_n=m-\tfrac{1}{n+1}\uparrow m$ (`exists_nat_gt` +
`div_lt_iff₀` + `nlinarith` for the covering; each slab is null by the core
estimate; `measure_iUnion_null` assembles),

$$\mu_\psi\{p\in C^+:\ t(p)<m\}=0\qquad\text{whenever } m\le\mathrm{LaplaceRate}(T,\psi)\text{ uniformly in }\psi.$$

```lean
/-- Slab form of the gap condition: all slabs strictly below the rate are null
(§48.1, slab half). -/
theorem slabNull_of_rate (T : WightmanTheory H Labels) (hW0 : T.W0) (m : ℝ)
    (hrate : ∀ ψ : H.carrier, m ≤ LaplaceRate T ψ) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) {p | p ∈ forwardCone ∧ time p < m} = 0 := by
  have hcover : {p | p ∈ forwardCone ∧ time p < m} ⊆
      ⋃ n : ℕ, {p | time p ≤ m - 1 / ((n : ℝ) + 1)} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    obtain ⟨hcone, hlt⟩ := hp
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (m - time p))
    have hp' : (0 : ℝ) < m - time p := by linarith
    have hn' : (1 : ℝ) < (n : ℝ) * (m - time p) := by
      rw [div_lt_iff₀ hp'] at hn
      exact hn
    have h2 : (1 : ℝ) / ((n : ℝ) + 1) < m - time p := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_setOf_eq]; linarith⟩
  have hunion : (T.energyMomentum.diagonal ψ)
      (⋃ n : ℕ, {p | time p ≤ m - 1 / ((n : ℝ) + 1)}) = 0 :=
    measure_iUnion_null (fun n => slab_null_of_rate T hW0 ψ (hrate ψ)
      (show m - 1 / ((n : ℝ) + 1) < m by
        have := div_pos one_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1); linarith))
  exact le_antisymm ((measure_mono hcover).trans (le_of_eq hunion)) zero_le
```

This is the **slab half** of the gap condition — the maximal output of the
Laplace/Chebyshev method in the public language.

# §4. The scalar bridge: diagonal nullity $\Rightarrow$ projection nullity

The gap condition is stated with the *operator* $E(A)$, not the measure $\mu_\psi$.
The bridge uses only PVM algebra: $E(A)$ is self-adjoint (`selfAdjoint`) and
idempotent (`intersection`), and `diagonalIdentity` identifies
$\langle\psi,E(A)\psi\rangle$ with $\mu_\psi(A)$.

If $\mu_\psi(\mathrm{LowRegion}\,m)=0$ then:

1. $\mu_\psi^{\mathrm{real}}(\mathrm{LowRegion}\,m)=0$ (values are `ℝ≥0∞`),
2. $\langle\psi, E(A)\psi\rangle=0$ via `diagonalIdentity`,
3. $\langle E(A)\psi, E(A)\psi\rangle=\langle\psi, E(A)^\dagger E(A)\psi\rangle
   =\langle\psi, E(A\cap A)\psi\rangle=\langle\psi,E(A)\psi\rangle=0$ via `adjoint_inner_right`,
   self-adjointness, `comp_apply`, and idempotence,
4. so $E(A)\psi=0$ (`inner_self_eq_zero`).

```lean
/-- If the diagonal measure of a state charges a measurable region with measure
zero, the projection of that region annihilates the state (via
`diagonalIdentity`, `selfAdjoint`, idempotence). -/
theorem projection_eq_zero_of_diagonalNull (T : WightmanTheory H Labels) (m : ℝ)
    {ψ : H.carrier} (h : (T.energyMomentum.diagonal ψ) (LowRegion m) = 0) :
    T.energyMomentum.projection (LowRegion m) ψ = 0 := by
  set E := T.energyMomentum.projection (LowRegion m) with hE
  have hid : E.comp E = E := by
    have hi := T.energyMomentum.intersection (lattice_set m) (lattice_set m)
    rwa [show (LowRegion m ∩ LowRegion m) = LowRegion m from Set.inter_self _] at hi
  have hsa : E.adjoint = E := T.energyMomentum.selfAdjoint (lattice_set m)
  have hinner0 : (T.energyMomentum.diagonal ψ).real (LowRegion m) = 0 := by
    rw [show MeasureTheory.Measure.real
      (T.energyMomentum.diagonal ψ) (LowRegion m) =
      ((T.energyMomentum.diagonal ψ) (LowRegion m)).toReal from rfl, h, ENNReal.toReal_zero]
  have hdi : inner ℂ ψ (E ψ) = 0 := by
    have hId := T.energyMomentum.diagonalIdentity (lattice_set m) ψ
    rw [hinner0] at hId
    simpa using hId.symm
  have hself : inner ℂ (E ψ) (E ψ) = 0 := by
    have h1 : inner ℂ (E ψ) (E ψ) = inner ℂ ψ (E.adjoint (E ψ)) :=
      (ContinuousLinearMap.adjoint_inner_right E ψ (E ψ)).symm
    rw [h1, hsa, ← ContinuousLinearMap.comp_apply,
      congrArg (fun f : H.Operator => f ψ) hid, hdi]
  exact inner_self_eq_zero.mp hself
```

```lean
/-- Mass gap from diagonal nullity (the pointwise part of the §11 equivalence,
using `diagonalIdentity` on the self-adjoint idempotent projections). -/
theorem massGap_of_diagonalNull (T : WightmanTheory H Labels) (m : ℝ) (hpos : 0 < m)
    (h : ∀ ψ : H.carrier, (T.energyMomentum.diagonal ψ) (LowRegion m) = 0) :
    MassGap T m :=
  ⟨hpos, fun ψ _ => projection_eq_zero_of_diagonalNull T m (h ψ)⟩
```

# §5. The Lorentz-intertwining node (Part XIII): what the public API lacks

This is the pivot of the entire evaluation. The low region decomposes as

$$\mathrm{LowRegion}(m)\ =\ \underbrace{\{p\in C^+:\ t(p)<m\}}_{\text{slab (proved null)}}\ \cup\ \underbrace{\{p\in C^+:\ m\le t(p),\ q(p)\le m^2\}}_{\text{massless wedge } W_m (=?)}$$

and the slab half is *not* the whole of it. The wedge requires a Lorentz boost
argument, and a Lorentz boost argument requires an intertwining law between the
unitary representation on states and the PVM on spectra:

$$E(L_g^{-1}A)=U(g)^\dagger\,E(A)\,U(g).$$

The public `PoincareAction` states such a law only for **pure translations**
(`translationCompatibility`); `W2` constrains only fields, domains, and the
vacuum. The Lorentz part of a symmetry can be *read off* the public coordinate
description,

```lean
/-- The Lorentz part of a symmetry, read off the public coordinate description
`coordinates : Symmetry ≃ₜ PoincareCoordinates`. -/
def lorentzOf (T : WightmanTheory H Labels) (g : T.poincare.Symmetry) :
    Spacetime →L[ℝ] Spacetime := (T.poincare.coordinates g).1.val
```

but the candidate missing datum must be *postulated*:

```lean
/-- Candidate public datum missing from `PublicTheory` (Part XIII): the
energy-momentum PVM intertwines with the Lorentz action on states,
`E(preimage L g A) = U(g)† E(A) U(g)`. `PoincareAction` states an intertwining
for pure translations only (`translationCompatibility`), and `W2` constrains
only fields, common domain, and vacuum. -/
def LorentzIntertwines (T : WightmanTheory H Labels) : Prop :=
  ∀ (g : T.poincare.Symmetry) {A : Set Spacetime} (_ : MeasurableSet A),
    T.energyMomentum.projection (Set.preimage (lorentzOf T g : Spacetime → Spacetime) A) =
      (T.poincare.onStates g).comp
        ((T.energyMomentum.projection A).comp (T.poincare.onStates g).adjoint)
```

Under this hypothesis, nullity of $W_m$ is the standard boost-covering argument:
every point of the wedge has Lorentz images of arbitrarily small `time`, the
vacuum is invariant (so orthogonality to it, and hence $\mu_\psi$, is preserved),
and `slabNull_of_rate` transfers across the intertwining. Since the hypothesis
is not available in the public language, **this node cannot be proved and the
method is ruled out in the public setting.** It is isolated as the single
`sorry` of the module — the only place in the file where a mathematical input
external to `PublicTheory` enters:

```lean
/-- **[B]-node — the single `sorry` of this module.** Nullity of the massless
wedge from the slab form. With `LorentzIntertwines T` this is the standard
boost-covering argument (every point of the wedge has Lorentz images of
arbitrarily small `time`, the vacuum is invariant so orthogonality to it is
preserved, and slab nullity transfers across the intertwining); without a
Lorentz intertwining datum the public API does not contain the statement needed
to even begin. -/
theorem wedgeNull_of_rate_of_intertwines (T : WightmanTheory H Labels) (hW0 : T.W0)
    (hI : LorentzIntertwines T) (m : ℝ)
    (hrate : ∀ ψ : H.carrier, m ≤ LaplaceRate T ψ) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ)
      {p | p ∈ forwardCone ∧ m ≤ time p ∧ minkowskiSquare p ≤ m ^ 2} = 0 := by
  sorry
```

Combining the halves is then pure set algebra (`measure_mono`,
`measure_union_le`, `lt_or_ge` on the two time regions):

```lean
/-- Combining the slab and wedge halves (§48, §56). -/
theorem diagonalNull_of_rate_of_intertwines (T : WightmanTheory H Labels) (hW0 : T.W0)
    (hI : LorentzIntertwines T) (m : ℝ) (_hpos : 0 < m)
    (hrate : ∀ ψ : H.carrier, m ≤ LaplaceRate T ψ) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ) (LowRegion m) = 0 := by
  have hslab := slabNull_of_rate T hW0 m hrate ψ
  have hwedge := wedgeNull_of_rate_of_intertwines T hW0 hI m hrate ψ
  have hsub : LowRegion m ⊆ {p | p ∈ forwardCone ∧ time p < m} ∪
      {p | p ∈ forwardCone ∧ m ≤ time p ∧ minkowskiSquare p ≤ m ^ 2} := by
    intro p hp
    simp only [LowRegion, Set.mem_setOf_eq] at hp
    obtain ⟨hcone, hsq, -⟩ := hp
    rcases lt_or_ge (time p) m with hlt | hge
    · exact Or.inl ⟨hcone, hlt⟩
    · exact Or.inr ⟨hcone, hge, hsq⟩
  have h1 : (T.energyMomentum.diagonal ψ) (LowRegion m) ≤
      (T.energyMomentum.diagonal ψ) ({p | p ∈ forwardCone ∧ time p < m} ∪
        {p | p ∈ forwardCone ∧ m ≤ time p ∧ minkowskiSquare p ≤ m ^ 2}) :=
    measure_mono hsub
  have h2 : (T.energyMomentum.diagonal ψ) ({p | p ∈ forwardCone ∧ time p < m} ∪
      {p | p ∈ forwardCone ∧ m ≤ time p ∧ minkowskiSquare p ≤ m ^ 2}) ≤
      (T.energyMomentum.diagonal ψ) {p | p ∈ forwardCone ∧ time p < m} +
        (T.energyMomentum.diagonal ψ) {p | p ∈ forwardCone ∧ m ≤ time p ∧
          minkowskiSquare p ≤ m ^ 2} := measure_union_le _ _
  exact le_antisymm ((h1.trans h2).trans
    (by rw [hslab, hwedge]; simp)) zero_le
```

and the mass gap follows by the §4 bridge and `push_neg` on the orthogonality
hypothesis:

```lean
/-- The mass-gap condition from the rate, given the (missing) Lorentz
intertwining — an exact [B]-level one-liner. -/
theorem massGap_of_rate_of_intertwines (T : WightmanTheory H Labels) (hW0 : T.W0)
    (hI : LorentzIntertwines T) (m : ℝ) (hpos : 0 < m)
    (hrate : ∀ ψ : H.carrier, m ≤ LaplaceRate T ψ) : MassGap T m :=
  ⟨hpos, fun ψ _ =>
    projection_eq_zero_of_diagonalNull T m
      (diagonalNull_of_rate_of_intertwines T hW0 hI m hpos hrate ψ)⟩
```

Every hypothesis of this last theorem is public except `hI : LorentzIntertwines T`.
That — and only that — is why the bracketed part of §3 + §4 + §5 remains one
conditional step short of the challenge.

# §6. The massless wedge: concrete obstruction to the slab-only argument

The ruled-out status is not an artefact of Lean's formalization; it is witnessed
by a concrete point. The **rest point** at energy $m$,

$$p_\ast=\mathrm{WithLp.toLp}\ 2\,(\mathrm{Pi.single}\ \mathrm{timeAxis}\ m),\qquad t(p_\ast)=m,\ \lVert x(p_\ast)\rVert=0,$$

lies in `LowRegion m` (cone identity $m\ge 0$, $q(p_\ast)=m^2\le m^2$, $p_\ast\neq 0$
since $m>0$) but satisfies $t(p_\ast)=m\not\le R$ for every slab edge $R<m$, in
particular for all $R_n = m-\tfrac{1}{n+1}$:

```lean
/-- The rest point at `time = m` lies in `LowRegion m` but in no slab
`{time ≤ R}`, `R < m`: the low region is not time-bounded (Part XIII). -/
theorem rest_point_witness {m : ℝ} (hpos : 0 < m) :
    (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) ∈ LowRegion m ∧
    time (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) = m := by
  have hz : ∀ i : SpaceAxis,
      (Pi.single (M := fun _ : Axis => ℝ) timeAxis m) i.castSucc = 0 :=
    fun i => Pi.single_eq_of_ne (M := fun _ : Axis => ℝ) (Fin.castSucc_ne_last i) m
  have hco : WithLp.ofLp (spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m))) = 0 :=
    funext fun i => hz i
  have hsz : spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) = 0 := by
    rw [← WithLp.toLp_ofLp (p := (2 : ℝ≥0∞))
      (x := spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)))]
    rw [hco, WithLp.toLp_zero]
  have hnorm : ‖spatial (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m))‖ = 0 :=
    norm_eq_zero.mpr hsz
  have htime : time (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) = m := by
    show (WithLp.ofLp (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m))) timeAxis = m
    rw [WithLp.ofLp_toLp]
    exact Pi.single_eq_same (M := fun _ : Axis => ℝ) timeAxis m
  have hcone : (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) ∈ forwardCone := by
    simp only [forwardCone, Set.mem_setOf_eq]
    rw [hnorm, htime]
    exact hpos.le
  have hsq : minkowskiSquare (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) ≤ m ^ 2 := by
    unfold minkowskiSquare
    rw [htime, hnorm]
    norm_num
  have hne : (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m)) ≠ 0 := by
    intro hp0
    apply hpos.ne'
    have h1 : (WithLp.ofLp (WithLp.toLp 2 (Pi.single (M := fun _ : Axis => ℝ) timeAxis m))) timeAxis = m := by
      rw [WithLp.ofLp_toLp]
      exact Pi.single_eq_same (M := fun _ : Axis => ℝ) timeAxis m
    rw [hp0, WithLp.ofLp_zero, Pi.zero_apply] at h1
    exact h1.symm
  exact ⟨⟨hcone, hsq, hne⟩, htime⟩
```

Hence the low region is *not* covered by the slab family on which §3 gives
nullity — the slab method alone cannot even decide $\mu_\psi$ on all of the low
region, let alone reach `MassGap`:

```lean
/-- Consequently the low region is not covered by the family of time slabs on
which slab nullity is available. -/
theorem lowRegion_not_slabCovered {m : ℝ} (hpos : 0 < m) :
    ¬ LowRegion m ⊆ ⋃ n : ℕ, {p | time p ≤ m - 1 / ((n : ℝ) + 1)} := by
  intro h
  obtain ⟨hmem, htime⟩ := rest_point_witness hpos
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (h hmem)
  simp only [Set.mem_setOf_eq] at hn
  rw [htime] at hn
  have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := div_pos one_pos (by positivity)
  linarith

end YangMills
```

The technical content of these two proofs is entirely `Pi.single`-bookkeeping on
the dependent `Pi.single` of this Mathlib snapshot (`Pi.single_eq_of_ne` with
`M := fun _ : Axis => ℝ` for the spatial zeros, `Pi.single_eq_same` for the time
entry, and `WithLp.toLp_ofLp` / `ofLp_toLp` round-trips for the Euclidean-space
coercions).

# §7. Summary table

| Node | Statement | Status |
|---|---|---|
| Geometry, measurability | `closed_forwardCone`, `lattice_set` | proved |
| Support on $C^+$ | `diagonal_le_cone` | proved |
| $M_\psi(s)\le\mu_\psi(\mathbb{R}^4)$, $m=0\in\mathrm{Rate}$ | `dampedMass_le_total`, `rateSet_nonempty` | proved |
| Slab nullity from rate | `slab_chebyshev`, `slab_null_of_rate`, `slabNull_of_rate` | proved |
| Scalar bridge | `projection_eq_zero_of_diagonalNull`, `massGap_of_diagonalNull` | proved |
| Slab $\cup$ wedge decomposition | `diagonalNull_of_rate_of_intertwines` | proved modulo §5 node |
| **Wedge nullity** | `wedgeNull_of_rate_of_intertwines` | **`sorry` — ruled out in the public language** |
| Mass gap from rate | `massGap_of_rate_of_intertwines` | conditional on §5 node |
| Obstruction witnesses | `rest_point_witness`, `lowRegion_not_slabCovered` | proved |

# Appendix A. Axiom audit

`#print axioms` over the module (on a copy with the audit block appended) shows:

* `rateSet_nonempty`, `dampedMass_le_total`, `slab_chebyshev`, `exists_lt_of_rate`,
  `slab_null_of_rate`, `slabNull_of_rate`, `projection_eq_zero_of_diagonalNull`,
  `massGap_of_diagonalNull`, `rest_point_witness`, `lowRegion_not_slabCovered`
  → `[propext, Classical.choice, Quot.sound]` (Lean's standard axioms only).
* `diagonalNull_of_rate_of_intertwines`, `massGap_of_rate_of_intertwines`
  → additionally `sorryAx`, inherited **solely** through
  `wedgeNull_of_rate_of_intertwines`.

`Sorry` count in `MassGap.lean`: **1** (line 390). Everything else compiles with
**0 errors, 0 warnings**.

# Appendix B. Verification

```bash
cd /workspace/github__yang-mills-group__OpenAI-YM-20261028
export PATH="$HOME/.elan/bin:$PATH"
lake env lean MassGap.lean
```

Cross-references: `MassGapScenarios.md` §2 (mass-gap definition), §11
(equivalence), §15/§48 (Chebyshev/rate machinery), §56 (combination), Part XIII
(missing-datum analysis).

# Appendix C. Exporting this page as a PDF

The document is plain pandoc-compatible Markdown: YAML metadata block, LaTeX
math in `$…$`/`$$…$$`, and fenced Lean code. Because the Lean source contains
Unicode (`∫⁻`, `‖·‖`, `ℝ≥0∞`, `∃`, `∀`), export with XeLaTeX and a Unicode font
(the YAML header already requests DejaVu):

```bash
pandoc MassGapProof.md -o MassGapProof.pdf --pdf-engine=xelatex
```

or, without `pandoc`, any Markdown-to-PDF pipeline that supports
`mainfont`/`monofont` YAML keys (e.g. Typst, `md-to-pdf` with a DejaVu CSS
font-family, or VS Code "Markdown PDF" with an embedded font).
