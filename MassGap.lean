import PublicTheory

/-!
# The mass gap in the challenge's public language

This module transcribes the mass-gap condition of `MassGapScenarios.md` §2 against
the actual signatures of `PublicTheory`, and compiles the analytically elementary
half of the reduction ([A]-level): an exponentially damped total mass
(`LaplaceRate > 0`) forces nullity of every time slab `{0 ≤ time < m}` on the
cone, and — given one further hypothesis — the mass gap itself.

The one hypothesis that cannot be discharged in the public language is the
Lorentz covariance of the energy-momentum PVM: `PublicTheory.PoincareAction`
intertwines `onStates` with `translations.operator` for **pure translations only**
(`translationCompatibility`); no axiom relates `onStates g` to `projection` for
a Lorentz transformation. The low region of the challenge statement is not
time-bounded (it contains the massless wedge `time ≥ m`, `minkowskiSquare ≤ m²`
inside the forward cone; concrete witness: the rest point
`WithLp.toLp 2 (Pi.single timeAxis m)` at `time = m`, see `rest_point_witness`
and `lowRegion_not_slabCovered`), so slab nullity alone does not close the
argument. Everything here is proved except exactly that node, which is isolated
recorded as the explicit axiom `wedgeNull_of_rate_of_intertwines` — the only
non-derived datum of this file (the statement `LorentzIntertwines T` that the
public API does not contain is assumed rather than proved; see the axiom
audit). The file itself compiles with no sorries and no warnings.

Section references are to `MassGapScenarios.md`.
-/
set_option autoImplicit false
noncomputable section
namespace YangMills

open MeasureTheory Set Function Filter
open scoped Topology NNReal ENNReal

variable {H : HilbertSpace} {Labels : FieldLabels}

/-! ## Geometry: continuity of the coordinate functions

Mirrors `YM.Mink.Geometry` (`clockL`, `restL`, `fun_prop` pattern), rebuilt on
the public `Spacetime` so that this file imports `PublicTheory` only. -/

/-- The time coordinate as a continuous linear functional. -/
def timeL : Spacetime →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap { toFun := time, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[fun_prop] lemma time_cont : Continuous time := timeL.continuous

/-- The spatial part as a continuous linear map. -/
def spatialL : Spacetime →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap { toFun := spatial, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[fun_prop] lemma spatial_cont : Continuous spatial := spatialL.continuous

@[fun_prop] lemma spatial_norm_cont : Continuous fun p : Spacetime => ‖spatial p‖ :=
  continuous_norm.comp spatial_cont

@[simp] lemma timeL_apply (p : Spacetime) : timeL p = time p := rfl

@[fun_prop] lemma continuous_minkowskiSquare : Continuous minkowskiSquare := by
  unfold minkowskiSquare; fun_prop

lemma closed_forwardCone : IsClosed forwardCone :=
  isClosed_le (by fun_prop) time_cont

theorem measurableSet_forwardCone : MeasurableSet forwardCone := closed_forwardCone.measurableSet

theorem measurableSet_time_le (R : ℝ) : MeasurableSet {p | time p ≤ R} :=
  (isClosed_le time_cont continuous_const).measurableSet

/-- The low region of the challenge statement (§2). -/
def LowRegion (m : ℝ) : Set Spacetime :=
  {p | p ∈ forwardCone ∧ minkowskiSquare p ≤ m ^ 2 ∧ p ≠ 0}

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

/-! ## Mass gap and the damped mass -/

/-- Mass gap in the public language (§2): the joint energy-momentum PVM
compressed to the orthocomplement of the vacuum avoids `LowRegion m`. -/
def MassGap (T : WightmanTheory H Labels) (m : ℝ) : Prop :=
  0 < m ∧ ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
    T.energyMomentum.projection (LowRegion m) ψ = 0

/-- The exponentially damped total mass of a state's diagonal measure (§48). -/
def dampedMass (T : WightmanTheory H Labels) (ψ : H.carrier) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp (-(s * time p))) ∂(T.energyMomentum.diagonal ψ)

/-- The uniform exponential bound defining the rate. -/
def RateBound (T : WightmanTheory H Labels) (ψ : H.carrier) (m : ℝ) : Prop :=
  0 ≤ m ∧ ∃ C : ℝ≥0, ∃ s₀ : ℝ, ∀ s ≥ s₀,
    dampedMass T ψ s ≤ ENNReal.ofReal ((C : ℝ) * Real.exp (-m * s))

/-- The uniform exponential rate of decay (§48): the supremum of all `m` with
`RateBound`. -/
def LaplaceRate (T : WightmanTheory H Labels) (ψ : H.carrier) : ℝ :=
  sSup {m : ℝ | RateBound T ψ m}

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

/-! ## The Chebyshev step: rate ⇒ slab nullity (§15, §48) -/

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

/-- A sub-supremum of the rate set. -/
theorem exists_lt_of_rate (T : WightmanTheory H Labels) (hW0 : T.W0) (ψ : H.carrier)
    {R m : ℝ} (hR : R < m) (hm : m ≤ LaplaceRate T ψ) :
    ∃ a : ℝ, a ∈ {m : ℝ | RateBound T ψ m} ∧ R < a :=
  exists_lt_of_lt_csSup (rateSet_nonempty T hW0 ψ) (lt_of_lt_of_le hR hm)

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

/-! ## The scalar bridge: diagonal nullity ⇒ projection nullity -/

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

/-- Mass gap from diagonal nullity (the pointwise part of the §11 equivalence,
using `diagonalIdentity` on the self-adjoint idempotent projections). -/
theorem massGap_of_diagonalNull (T : WightmanTheory H Labels) (m : ℝ) (hpos : 0 < m)
    (h : ∀ ψ : H.carrier, (T.energyMomentum.diagonal ψ) (LowRegion m) = 0) :
    MassGap T m :=
  ⟨hpos, fun ψ _ => projection_eq_zero_of_diagonalNull T m (h ψ)⟩

/-! ## The Lorentz-intertwining node (Part XIII): what the public API lacks -/

/-- The Lorentz part of a symmetry, read off the public coordinate description
`coordinates : Symmetry ≃ₜ PoincareCoordinates`. -/
def lorentzOf (T : WightmanTheory H Labels) (g : T.poincare.Symmetry) :
    Spacetime →L[ℝ] Spacetime := (T.poincare.coordinates g).1.val

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

/-- **[B]-node — the one datum the public API lacks, declared as an explicit
axiom.** Nullity of the massless wedge from the slab form. With
`LorentzIntertwines T` this is the standard boost-covering argument (every point
of the wedge has Lorentz images of arbitrarily small `time`, the vacuum is
invariant so orthogonality to it is preserved, and slab nullity transfers across
the intertwining); without a Lorentz intertwining datum the public API does not
contain the statement needed to even begin, so it is **assumed** here — visibly,
under its own name, as the missing datum the public API must eventually supply. -/
axiom wedgeNull_of_rate_of_intertwines {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hI : LorentzIntertwines T)
    (m : ℝ) (hrate : ∀ ψ : H.carrier, m ≤ LaplaceRate T ψ) (ψ : H.carrier) :
    (T.energyMomentum.diagonal ψ)
      {p | p ∈ forwardCone ∧ m ≤ time p ∧ minkowskiSquare p ≤ m ^ 2} = 0

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

/-- The mass-gap condition from the rate, given the (missing) Lorentz
intertwining — an exact [B]-level one-liner. -/
theorem massGap_of_rate_of_intertwines (T : WightmanTheory H Labels) (hW0 : T.W0)
    (hI : LorentzIntertwines T) (m : ℝ) (hpos : 0 < m)
    (hrate : ∀ ψ : H.carrier, m ≤ LaplaceRate T ψ) : MassGap T m :=
  ⟨hpos, fun ψ _ =>
    projection_eq_zero_of_diagonalNull T m
      (diagonalNull_of_rate_of_intertwines T hW0 hI m hpos hrate ψ)⟩

/-! ## The massless wedge: concrete obstruction to the slab-only argument -/

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
