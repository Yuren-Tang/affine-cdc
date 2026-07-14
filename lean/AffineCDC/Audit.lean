import AffineCDC

/-!
# Audit

`lake env lean AffineCDC/Audit.lean` prints the axiom footprint of the
headline results across the whole development: T1–T7, the dart-level Fano
compatibility/cycle-cover endpoints, the internalized comparison lemma, and
the Graph-level intermediate macro-Port theorem `cubic_flow_cdc`.  Expected
output for every line: `[propext, Classical.choice, Quot.sound]`.

(`import AffineCDC` (the root aggregate) already transitively imports
`AffineCDC.Port`, so no separate import of `Port` is needed here.)

Source scan (should print nothing):
`rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' AffineCDC/`
-/

-- T1: local classification
#print axioms AffineCDC.localEquiv
#print axioms AffineCDC.covers_localFamily_iff
#print axioms AffineCDC.IsPlane.of_finrank_eq_two

-- T2: naturality and torsor representation
#print axioms AffineCDC.localFamily_translate
#print axioms AffineCDC.mapFamily_localFamily
#print axioms AffineCDC.localAffineEquiv

-- T3: edge quotients
#print axioms AffineCDC.coset_eq_pair
#print axioms AffineCDC.lineLift_unique
#print axioms AffineCDC.eq_kappa_of_ne_zero
#print axioms AffineCDC.existsUnique_label

-- A3: opposite fibre
#print axioms AffineCDC.localFamily_points

-- T4 (abstract): gauge classification
#print axioms AffineCDC.gaugeEquiv_iff
#print axioms AffineCDC.gaugeClassesEquiv
#print axioms AffineCDC.exists_solution_iff_forall_dual

-- T5: cross-pairing bit
#print axioms AffineCDC.cross_eq
#print axioms AffineCDC.crossBitL
#print axioms AffineCDC.crossBit_eq_zero_iff

-- T6: uniqueness of the invariant functional (arbitrary Γ)
#print axioms AffineCDC.crossBit_baseConfig
#print axioms AffineCDC.ShearInvariant.eq_smul_crossBitL
#print axioms AffineCDC.ShearInvariant.eq_zero_or_eq_crossBitL

-- T7 F1: branching identity (codim-one core) + rank bridge converse
#print axioms AffineCDC.annihilator_unique
#print axioms AffineCDC.crossBit_eq_parity
#print axioms AffineCDC.IsPlane.finrank_eq_two

-- T7 F0/C3/F2: dart layer and the Fano compatibility theorem (endpoint)
#print axioms AffineCDC.DartFlow.cfam_eq_kappa
#print axioms AffineCDC.DartFlow.exists_gluing
#print axioms AffineCDC.DartFlow.exists_gluing_of_finrank_three

-- F3 and the internalized comparison
#print axioms AffineCDC.DartFlow.exists_gluing_labels
#print axioms AffineCDC.slotFamily_eq_localFamily

-- G: the indexed dart cover (dart-level; see cubic_flow_cdc below for the
-- graph-level Statement.IsCycleDoubleCover this data is used to extract)
#print axioms AffineCDC.DartFlow.Msupp_sigma
#print axioms AffineCDC.DartFlow.Msupp_vertex_unique
#print axioms AffineCDC.DartFlow.exists_indexed_dart_cover

-- P1: intermediate macro-Port theorem (cubic + F2^3-flow => CDC)
#check @AffineCDC.Port.cubic_flow_cdc
#print axioms AffineCDC.Port.cubic_flow_cdc
