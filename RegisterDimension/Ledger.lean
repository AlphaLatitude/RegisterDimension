import RegisterDimension

/-! # The axiom ledger of the check of *The Dimension of Space from the Granularity of Hilbert Space*
(v16-34)

For every main theorem, the axioms its proof depends on.  A physical input is never an axiom
here: it is a named hypothesis in the statement of the theorem that uses it.  The expected output
for every line is `[propext, Classical.choice, Quot.sound]`, the logical minimum of classical
mathematics in Lean; `sorryAx` would flag an unfinished proof. -/

-- Secs. II–III, one ring: Born's rule, the notch, modes, momentum, the Weyl pair, the doublet
#print axioms Register.Ring.phase_succ
#print axioms Register.Ring.born
#print axioms Register.Ring.mode_periodic
#print axioms Register.Ring.shift_mode
#print axioms Register.Ring.root_add
#print axioms Register.Ring.root_injective
#print axioms Register.Ring.norm_mode
#print axioms Register.Ring.mode_uniform
#print axioms Register.Ring.joint_mode
#print axioms Register.Ring.shift_eigen
#print axioms Register.Ring.weyl
#print axioms Register.Ring.doublet_branches
#print axioms Register.Ring.doublet_mean

-- Sec. IV, offsets: a closed sum around a ring is a gauge invariant
#print axioms Register.Offsets.pathSum_coboundary
#print axioms Register.Offsets.closed_coboundary
#print axioms Register.Offsets.closed_sum_invariant
#print axioms Register.Offsets.no_single_offset
#print axioms Register.Offsets.quantum_changes_closed_sum
#print axioms Register.Offsets.ring_offsets

-- Sec. IV, the vertex: the alphabet, the span, and `d = 3` from Postulate 2
#print axioms Register.Vertex.alphabet_card
#print axioms Register.Vertex.alphabet_card_zero
#print axioms Register.Vertex.cells_card
#print axioms Register.Vertex.span_of_postulate
#print axioms Register.Vertex.finrank_span_le_of_sum_zero
#print axioms Register.Vertex.finrank_span_eq_of_sum_zero
#print axioms Register.Vertex.dimension_eq_legs
#print axioms Register.Vertex.three
#print axioms Register.Vertex.orientation_not_counted
#print axioms Register.Vertex.coincidence
#print axioms Register.Vertex.coincidence_two_cells
#print axioms Register.Vertex.eigenspace_preserved

-- Secs. II and IV, the setting and conservation from Postulate 1
#print axioms Register.Conservation.shifts_commute
#print axioms Register.Conservation.turn_comm
#print axioms Register.Conservation.eigenvalue_root
#print axioms Register.Conservation.productMode_shift
#print axioms Register.Conservation.root_sum
#print axioms Register.Conservation.jointMode_shift
#print axioms Register.Conservation.root_eq_iff
#print axioms Register.Conservation.uniform_mode_zero
#print axioms Register.Conservation.total_mode_conserved
#print axioms Register.Conservation.vertex_exists
#print axioms Register.Conservation.eq_of_window
#print axioms Register.Conservation.three_leg_conservation
#print axioms Register.Conservation.sum_zero_of_components

-- Sec. IV, `d = 3` from the two postulates
#print axioms Register.Derivation.Emission.conserve
#print axioms Register.Derivation.Emission.finrank_legs
#print axioms Register.Derivation.three_from_postulates
#print axioms Register.Derivation.model_consistent

-- Sec. IV, two rings share at most two cells
#print axioms Register.Planes.two_planes_meet

-- Secs. V–VII, the sphere: the areas, the pixel counts, the cell
#print axioms Register.Sphere.u_two_sphere
#print axioms Register.Sphere.cos_sq_half_eq
#print axioms Register.Sphere.band_area
#print axioms Register.Sphere.Ω_two
#print axioms Register.Sphere.Ω_three
#print axioms Register.Sphere.Ω_four
#print axioms Register.Sphere.Ω_five
#print axioms Register.Sphere.Npix_two
#print axioms Register.Sphere.Npix_three
#print axioms Register.Sphere.Npix_four
#print axioms Register.Sphere.Npix_five
#print axioms Register.Sphere.C_two
#print axioms Register.Sphere.C_three
#print axioms Register.Sphere.C_four
#print axioms Register.Sphere.cell_area
#print axioms Register.Sphere.pixel_subtends_notch

-- Sec. VI, the relaxed count: bounds, the root, its bracket, its uniqueness, its shifts
#print axioms Register.Root.f_nonpos
#print axioms Register.Root.f_ge
#print axioms Register.Root.slope_le_log
#print axioms Register.Root.logC_eq
#print axioms Register.Root.logC_nonpos
#print axioms Register.Root.logC_ge
#print axioms Register.Root.logC_strictAnti
#print axioms Register.Root.g_two
#print axioms Register.Root.g_four_eq
#print axioms Register.Root.g_four
#print axioms Register.Root.root_exists_general
#print axioms Register.Root.root_exists
#print axioms Register.Root.g_strictMono
#print axioms Register.Root.root_bound
#print axioms Register.Root.f_near_three_halves
#print axioms Register.Root.logC_near_three
#print axioms Register.Root.g_at_bracket
#print axioms Register.Root.root_bracket
#print axioms Register.Root.unique_root
#print axioms Register.Root.g_slope
#print axioms Register.Root.pixel_shift
#print axioms Register.Root.seven_halves_factor
#print axioms Register.Root.five_halves_factor

-- The numbers of the paper, for every L between 10^61 and 10^62
#print axioms Register.DimensionNumerics.inv_pi_val
#print axioms Register.DimensionNumerics.pi_val
#print axioms Register.DimensionNumerics.log_pi_bounds
#print axioms Register.DimensionNumerics.log_ten_bounds
#print axioms Register.DimensionNumerics.log_L_range
#print axioms Register.DimensionNumerics.leading_term_range
#print axioms Register.DimensionNumerics.bound_value_range
#print axioms Register.DimensionNumerics.pixel_choice_range
#print axioms Register.DimensionNumerics.root_range
#print axioms Register.DimensionNumerics.uniqueness_range
#print axioms Register.DimensionNumerics.pixel_shift_range
#print axioms Register.DimensionNumerics.seven_halves_range
#print axioms Register.DimensionNumerics.five_halves_range
#print axioms Register.DimensionNumerics.capacity_range
