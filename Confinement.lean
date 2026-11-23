import ChallengeSpec

/-!
# The confinement node in the challenge's public language

This module evaluates the methodology that would lead from the repository's
public language to the statement that fundamental theoretical particles
(quarks) cannot exist freely and are always confined within color-bound
quantum states.

The machine-checked content:

* `FreeLabel` / `ConfinedLabel`: spectral confinement of a field label —
  expressible in the public language (`PublicTheory` + `PublicWilson`,
  imported through `ChallengeSpec`), using only the joint energy-momentum
  PVM and the positive-mass shells `massShell m`.
* `freeLabel_gauge_trivial`: under the candidate gauge interface
  `GaugeIntertwinesTypeDef` (unitary gauge action fixing the vacuum and
  preserving the field domain, gauge covariance of the fields, and
  separation of distinct labels by shared nonzero vacuum excitations),
  every spectrally free label is gauge-fixed. No free particle carries color.
* `confined_of_colorCharged`: hence every label moved by some gauge
  transformation is confined — the confinement of quarks in the public
  spectral form — conditional on the interface.
* The interface itself, together with the Gauss-law-shaped neutrality of
  on-shell states (`ShellNeutral`), is not a datum of the public language:
  no structure field of `PublicTheory.WightmanTheory` connects the theory
  to `GaugeGroup` (the gauge group is an orphan structure there), and every
  hypothesis of `ChallengeSpec.JointExistence` — `WilsonRegularity`,
  `Hierarchy.Properties` (`wilson`, `reconstruction`, `ope`, `nonfree`) —
  is a vacuum correlation of gauge-invariant insertions, blind to an
  arbitrarily adjoined decoupled colored sector.

Consequently the methodology is ruled out as a public-language derivation
of confinement: it neither names a quark nor excludes a free colored
sector. This file contains no `sorry` and no `axiom`; the missing datum is
carried visibly by the hypotheses of the bridge theorems.
-/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory Set Function Filter
open scoped Topology NNReal ENNReal

variable {H : HilbertSpace} {Labels : FieldLabels}

/-! ## Geometry copied from the public coordinates -/

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

lemma closed_forwardCone : IsClosed forwardCone :=
  isClosed_le (by fun_prop) time_cont

theorem measurableSet_forwardCone : MeasurableSet forwardCone :=
  closed_forwardCone.measurableSet

@[fun_prop] lemma continuous_minkowskiSquare : Continuous minkowskiSquare := by
  unfold minkowskiSquare; fun_prop

/-! ## The positive-mass shell in the public language -/

/-- The positive-mass shell: forward-cone points of Minkowski square `m^2`. -/
def massShell (m : ℝ) : Set Spacetime :=
  {p | p ∈ forwardCone ∧ minkowskiSquare p = m ^ 2 ∧ p ≠ 0}

theorem measurableSet_massShell (m : ℝ) : MeasurableSet (massShell m) := by
  have hEq : massShell m =
      forwardCone ∩ {p : Spacetime | minkowskiSquare p = m ^ 2} ∩
        Set.compl {(0 : Spacetime)} := by
    ext p
    simp only [massShell, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((measurableSet_forwardCone.inter
    (isClosed_eq continuous_minkowskiSquare continuous_const).measurableSet).inter
    (measurableSet_singleton (0 : Spacetime)).compl)

/-! ## Label excitations and spectral freeness -/

/-- One smeared field application to the vacuum: the state `φ_ℓ(f)Ω`. -/
def excitation (T : WightmanTheory H Labels) (ℓ : Labels.carrier)
    (f : TestFunction) : H.carrier := (T.fields.field ℓ f T.fields.vacuum).1

/-- The zero state has zero spectral measure. -/
theorem diagonal_zero_measure (T : WightmanTheory H Labels) (m : ℝ) :
    (T.energyMomentum.diagonal 0) (massShell m) = 0 := by
  have hreal : (T.energyMomentum.diagonal 0).real (massShell m) = 0 := by
    have h := T.energyMomentum.diagonalIdentity (measurableSet_massShell m) (0 : H.carrier)
    simp only [map_zero, inner_zero_left] at h
    exact Complex.ofReal_eq_zero.mp h
  have hne : (T.energyMomentum.diagonal 0) (massShell m) ≠ ∞ := measure_ne_top _ _
  exact measureReal_eq_zero_iff hne |>.mp hreal

/-- A spectrally charged excitation is a nonzero state. -/
theorem excitation_nonzero_of_free {T : WightmanTheory H Labels}
    {ℓ : Labels.carrier} {f : TestFunction} {m : ℝ}
    (hne : (T.energyMomentum.diagonal (excitation T ℓ f)) (massShell m) ≠ 0) :
    excitation T ℓ f ≠ 0 := by
  intro h0
  rw [h0] at hne
  exact hne (diagonal_zero_measure T m)

/-- A label is **spectrally free** if some of its vacuum excitations charge a
positive-mass shell of the joint energy-momentum PVM: the public-language
form of "this label has free one-particle-like carriers". -/
def FreeLabel (T : WightmanTheory H Labels) (ℓ : Labels.carrier) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∃ f : TestFunction,
    (T.energyMomentum.diagonal (excitation T ℓ f)) (massShell m) ≠ 0

/-- Spectral confinement of a label: no free on-shell carrier at all. -/
def ConfinedLabel (T : WightmanTheory H Labels) (ℓ : Labels.carrier) : Prop :=
  ¬ FreeLabel T ℓ

/-! ## The candidate gauge interface — the datum the public language lacks -/

/-- Candidate missing interface between `WightmanTheory` and `GaugeGroup`:
a unitary gauge action `U` on states fixing the vacuum and preserving the
field domain, an induced label action `ρ`, gauge covariance of the fields,
and separation of distinct labels by shared nonzero vacuum excitations.
No structure field of `PublicTheory` carries any of this. -/
structure GaugeIntertwinesTypeDef (T : WightmanTheory H Labels)
    (gauge : GaugeGroup) where
  ρ : ↥gauge.image → Labels.carrier ≃ₗ[ℂ] Labels.carrier
  U : ↥gauge.image → H.Operator
  vacuumFixed (g : ↥gauge.image) : U g T.fields.vacuum.1 = T.fields.vacuum.1
  domainMapsTo (g : ↥gauge.image) (v : H.carrier) :
    v ∈ T.fields.domain → U g v ∈ T.fields.domain
  covariance (g : ↥gauge.image) (ℓ : Labels.carrier) (f : TestFunction)
      (v : ↥T.fields.domain) :
    U g (T.fields.field ℓ f v).1 =
      (T.fields.field (ρ g ℓ) f
        ⟨U g v.1, domainMapsTo g v.1 v.2⟩).1
  separates (ℓ ℓ' : Labels.carrier) (f : TestFunction) :
    excitation T ℓ f = excitation T ℓ' f → excitation T ℓ f ≠ 0 → ℓ = ℓ'

/-- The Gauss-law-shaped datum: on-shell excitations are gauge-neutral. -/
def ShellNeutral (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (U : ↥gauge.image → H.Operator) : Prop :=
  ∀ (g : ↥gauge.image) (ℓ : Labels.carrier) (f : TestFunction) (m : ℝ),
    0 < m →
    (T.energyMomentum.diagonal (excitation T ℓ f)) (massShell m) ≠ 0 →
    U g (excitation T ℓ f) = excitation T ℓ f

/-- A label is color-carrying when some gauge transformation moves it. -/
def ColorCharged (gauge : GaugeGroup) (ρ : ↥gauge.image → Labels.carrier ≃ₗ[ℂ] Labels.carrier)
    (ℓ : Labels.carrier) : Prop := ∃ g : ↥gauge.image, ρ g ℓ ≠ ℓ

/-! ## The confinement theorems (modulo the interface) -/

/-- Gauge covariance of the vacuum excitation. -/
lemma gauge_excitation (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (I : GaugeIntertwinesTypeDef T gauge) (g : ↥gauge.image) (ℓ : Labels.carrier)
    (f : TestFunction) :
    I.U g (excitation T ℓ f) = excitation T (I.ρ g ℓ) f := by
  have hc := I.covariance g ℓ f T.fields.vacuum
  show I.U g (T.fields.field ℓ f T.fields.vacuum).1 =
    (T.fields.field (I.ρ g ℓ) f T.fields.vacuum).1
  rw [hc]
  exact congrArg (fun v : ↥T.fields.domain => (T.fields.field (I.ρ g ℓ) f v).1)
    (Subtype.ext (I.vacuumFixed g))

/-- Every spectrally free label is gauge-fixed: no free particle carries
color. This is the Gauss-law argument in spectral form. -/
theorem freeLabel_gauge_trivial (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (I : GaugeIntertwinesTypeDef T gauge) (hphys : ShellNeutral T gauge I.U)
    {ℓ : Labels.carrier} (hfree : FreeLabel T ℓ) (g : ↥gauge.image) :
    I.ρ g ℓ = ℓ := by
  obtain ⟨m, hm, f, hne⟩ := hfree
  have h0 : excitation T ℓ f ≠ 0 := excitation_nonzero_of_free hne
  have hh : excitation T (I.ρ g ℓ) f = excitation T ℓ f :=
    (gauge_excitation T gauge I g ℓ f).symm.trans (hphys g ℓ f m hm hne)
  exact (I.separates ℓ (I.ρ g ℓ) f hh.symm h0).symm

/-- The confinement of quarks in the public spectral form: every
color-carrying label is confined. -/
theorem confined_of_colorCharged (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (I : GaugeIntertwinesTypeDef T gauge) (hphys : ShellNeutral T gauge I.U)
    {ℓ : Labels.carrier} (hcharge : ColorCharged gauge I.ρ ℓ)
    (hfree : FreeLabel T ℓ) : False := by
  obtain ⟨g, hne⟩ := hcharge
  exact hne (freeLabel_gauge_trivial T gauge I hphys hfree g)

/-! ## What the mass gap does and does not exclude -/

/-- The low region of the challenge statement (duplicated from `MassGap.lean`,
which is not a library root). -/
def LowRegion (m : ℝ) : Set Spacetime :=
  {p | p ∈ forwardCone ∧ minkowskiSquare p ≤ m ^ 2 ∧ p ≠ 0}

/-- Mass gap in the public language (duplicated from `MassGap.lean`). -/
def GapCondition (T : WightmanTheory H Labels) (m : ℝ) : Prop :=
  0 < m ∧ ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
    T.energyMomentum.projection (LowRegion m) ψ = 0

theorem lattice_set (m : ℝ) : MeasurableSet (LowRegion m) := by
  have hEq : LowRegion m =
      forwardCone ∩ {p : Spacetime | minkowskiSquare p ≤ m ^ 2} ∩
        Set.compl {(0 : Spacetime)} := by
    ext p
    simp only [LowRegion, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((measurableSet_forwardCone.inter
    (isClosed_le continuous_minkowskiSquare continuous_const).measurableSet).inter
    (measurableSet_singleton (0 : Spacetime)).compl)

theorem pow_le_of_lt_positive {μ m : ℝ} (hμ : 0 < μ) (hμlt : μ < m) : μ ^ 2 ≤ m ^ 2 := by
  have hle : μ ≤ m := hμlt.le
  nlinarith [hμ.le, hle]

theorem inter_massShell_lowRegion {μ m : ℝ} (hμ : 0 < μ) (hμlt : μ < m) :
    massShell μ ∩ LowRegion m = massShell μ := by
  ext p
  simp only [Set.mem_inter_iff, massShell, LowRegion, Set.mem_setOf_eq]
  refine ⟨fun ⟨hsh, _⟩ => hsh, fun hsh => ⟨hsh, ?_⟩⟩
  obtain ⟨hcone, hsq, hne0⟩ := hsh
  exact ⟨hcone, le_trans (le_of_eq hsq) (pow_le_of_lt_positive hμ hμlt), hne0⟩

/-- **The gap excludes light free carriers, and only them.** Under the mass
gap at `m`, a vacuum-centered label excitation charging the `μ`-shell forces
`μ ≥ m`: no free colored particle below the gap can exist in the low region,
while free colored particles heavier than the gap are untouched — so the
mass-gap methodology alone cannot establish confinement. -/
theorem free_label_mass_ge_of_massGap (T : WightmanTheory H Labels) {m : ℝ}
    (hmg : GapCondition T m) {ℓ : Labels.carrier} {f : TestFunction} {μ : ℝ}
    (hμ : 0 < μ) (hμlt : μ < m)
    (hcenter : inner ℂ T.fields.vacuum.1 (excitation T ℓ f) = 0)
    (hne : (T.energyMomentum.diagonal (excitation T ℓ f)) (massShell μ) ≠ 0) : False := by
  obtain ⟨-, hall⟩ := hmg
  set v := excitation T ℓ f with hv
  have hproj : T.energyMomentum.projection (LowRegion m) v = 0 := hall v hcenter
  have hint := T.energyMomentum.intersection (measurableSet_massShell μ) (lattice_set m)
  rw [inter_massShell_lowRegion hμ hμlt] at hint
  have hshell : T.energyMomentum.projection (massShell μ) v = 0 := by
    have hEq : T.energyMomentum.projection (massShell μ) =
        (T.energyMomentum.projection (massShell μ)).comp
          (T.energyMomentum.projection (LowRegion m)) := hint.symm
    rw [hEq, ContinuousLinearMap.comp_apply, hproj]
    exact map_zero _
  have hreal : (T.energyMomentum.diagonal v).real (massShell μ) = 0 := by
    have h := T.energyMomentum.diagonalIdentity (measurableSet_massShell μ) v
    rw [hshell] at h
    simp only [inner_zero_right] at h
    exact Complex.ofReal_eq_zero.mp h
  have hneTop : (T.energyMomentum.diagonal v) (massShell μ) ≠ ⊤ := measure_ne_top _ _
  exact hne (measureReal_eq_zero_iff hneTop |>.mp hreal)

/-- Contrapositive summary: freeness forces color-neutrality — every free
particle is a color-bound (gauge-singlet) object. -/
theorem free_means_colorless (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (I : GaugeIntertwinesTypeDef T gauge) (hphys : ShellNeutral T gauge I.U)
    {ℓ : Labels.carrier} (hfree : FreeLabel T ℓ) :
    ¬ ColorCharged gauge I.ρ ℓ := by
  intro hc
  obtain ⟨g, hne⟩ := hc
  exact hne (freeLabel_gauge_trivial T gauge I hphys hfree g)

end YangMills
end
