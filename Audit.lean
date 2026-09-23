import RootedKP

-- Axiom reports are recursive: they include dependencies of these theorems.
#print axioms RootedKP.Heaps.Heap.group_injective
#print axioms RootedKP.Heaps.Heap.deleteRoot_injective_on_root
#print axioms RootedKP.Heaps.encodeRooted_injective
#print axioms RootedKP.Heaps.weight_encodeRooted
#print axioms RootedKP.Heaps.boundedHeapMass_step
#print axioms RootedKP.Heaps.rooted_heap_KP_of_criterion
#print axioms RootedKP.count_cut_marks
#print axioms RootedKP.cut_mass_summable
#print axioms RootedKP.root_mass_le_of_length_bounds
#print axioms RootedKP.AKLT.scalarSum_by_root
#print axioms RootedKP.AKLT.scalarSum_count_marks
#print axioms RootedKP.AKLT.fixedRootMass_le_of_uniform_kp
#print axioms RootedKP.AKLT.uniform_rooted_summability_of_kp_and_root_mass
#print axioms RootedKP.AKLT.rootBudget_le_weightCap
#print axioms RootedKP.AKLT.rootBudget_path_le_weightCap
#print axioms RootedKP.AKLT.traversalEdges_card
#print axioms RootedKP.AKLT.loopEdges_card
#print axioms RootedKP.AKLT.Polymer.length_ge_three
#print axioms RootedKP.AKLT.Polymer.loop_length_even
#print axioms RootedKP.AKLT.Polymer.loop_length_ge_six
#print axioms RootedKP.AKLT.face_probe_for_edge
#print axioms RootedKP.AKLT.scalarSum_le_of_uniform_kp
#print axioms RootedKP.AKLT.uniform_rooted_summability_of_uniform_kp
#print axioms RootedKP.Honeycomb.faceHalo_iff_minkowski
#print axioms RootedKP.Honeycomb.SunWalk.between_leaves_length
#print axioms RootedKP.Honeycomb.nonadjacent_sides_separated
#print axioms RootedKP.Honeycomb.edge_transitive
#print axioms RootedKP.Honeycomb.collar_edge_cell_cover
#print axioms RootedKP.Honeycomb.global_cell_gluing
#print axioms RootedKP.Honeycomb.collarMap_contracts_actual_edge
#print axioms RootedKP.Honeycomb.collarMap_fixes_inner
#print axioms RootedKP.Honeycomb.collarMap_image_inner
#print axioms RootedKP.Arithmetic.all_seven_below_one
#print axioms RootedKP.Arithmetic.long_weight_bound
#print axioms RootedKP.Arithmetic.first_moment_tail
#print axioms RootedKP.Arithmetic.cumulative_count_comparison
#print axioms RootedKP.LoopCounts.loop_input_prefix
#print axioms RootedKP.LoopCounts.anchoredEvenMass_le
#print axioms RootedKP.LoopCounts.anchoredEvenAnalyticMass_le
#print axioms RootedKP.AKLT.uniformKP_of_unweighted_path_counts
#print axioms RootedKP.AKLT.scalar_bound_of_unweighted_path_counts
#print axioms RootedKP.AKLT.loop_kindMass_le_allowance
#print axioms RootedKP.AKLT.loopsOnEdge_card_le
#print axioms RootedKP.AKLT.loop_edge_mass_le
#print axioms RootedKP.AKLT.tail_envelope_le_of_counts
#print axioms RootedKP.AKLT.short_envelope_le_of_cumulative
#print axioms RootedKP.AKLT.long_envelope_of_length_counts
#print axioms RootedKP.Arithmetic.longUniformAllowance_le_cost
#print axioms RootedKP.EndpointConvolution.endpoint_convolution
#print axioms RootedKP.Honeycomb.BoundaryPath.trimmed_edge_in_collar
#print axioms RootedKP.Honeycomb.BoundaryPath.short_even_retraction_contracts
#print axioms RootedKP.Honeycomb.BoundaryCycle.inner_iff_halfopen
#print axioms RootedKP.Honeycomb.BoundaryCycle.halfopen_injective
#print axioms RootedKP.Honeycomb.BoundaryCycle.collapsed_total
#print axioms RootedKP.BoundaryCounts.mem_cornerPaths_iff
#print axioms RootedKP.BoundaryCounts.cornerCount_eq_card
#print axioms RootedKP.BoundaryCounts.corner_prefix_five_matches_arithmetic
#print axioms RootedKP.BoundaryCounts.side_prefix_three_matches_arithmetic
#print axioms RootedKP.BoundaryCounts.upper_same_side_count_le
#print axioms RootedKP.BoundaryCounts.left_same_side_count_le
#print axioms RootedKP.Honeycomb.BoundaryCycle.coordinate_injective
#print axioms RootedKP.Honeycomb.BoundaryCycle.coordinate_successor
#print axioms RootedKP.Honeycomb.BoundaryCycle.coordinate_surjective
#print axioms RootedKP.Honeycomb.BoundaryCycle.retraction_coordinate_loss
#print axioms RootedKP.Honeycomb.BoundaryCycle.preimage_of_nonwrapping_arc
#print axioms RootedKP.BoundaryCounts.endpointCount_le_from_ten
#print axioms RootedKP.BoundaryCounts.side_global_prefix_bound
#print axioms RootedKP.BoundaryCounts.corner_global_prefix_bound
#print axioms RootedKP.Honeycomb.BoundaryCycle.adjacent_parameters

-- Print the final theorem's assumptions as well as its axiom dependencies.
#print axioms RootedKP.BoundaryCounts.side_prefix_checks
#print axioms RootedKP.BoundaryCounts.corner_prefix_checks
#print axioms RootedKP.BoundaryCounts.full_corner_table
#print axioms RootedKP.BoundaryCounts.full_side_table
#print axioms RootedKP.RegionalEndpoints.count_le_envelope
#print axioms RootedKP.AKLT.tail_length_count_bound
#print axioms RootedKP.AKLT.regional_path_tail_bound
#print axioms RootedKP.AKLT.even_root_family_count
#print axioms RootedKP.AKLT.global_odd_family_count
#print axioms RootedKP.AKLT.odd_root_family_count
#print axioms RootedKP.AKLT.long_odd_length_bound
#print axioms RootedKP.AKLT.long_even_length_bound
#print axioms RootedKP.AKLT.six_root_family_count
#print axioms RootedKP.AKLT.long_six_length_bound
#print axioms RootedKP.ShortRootCharts.w3_count_at
#print axioms RootedKP.AKLT.three_root_cumulative
#print axioms RootedKP.AKLT.short_path_root_catalog
#print axioms RootedKP.AKLT.short_loop_root_catalog
#print axioms RootedKP.ShortRootRepresentatives.fastCatalogCount_eq
#print axioms RootedKP.AKLT.unweighted_counts_of_catalog_and_four
#print axioms RootedKP.AKLT.scalar_bound_of_catalog_and_four
#print axioms RootedKP.AKLT.short_geometric_suffix
#print axioms RootedKP.AKLT.hybrid_cumulative_of_prefix
#print axioms RootedKP.AKLT.hybrid_allowance_le_cost
#print axioms RootedKP.AKLT.uniformKP_of_prefix_catalog_and_four
#print axioms RootedKP.AKLT.scalar_bound_of_prefix_catalog_and_four
#print axioms RootedKP.AKLT.uniform_rooted_summability_of_prefix_catalog_and_four
#print axioms RootedKP.Honeycomb.ZeroCollar.collar_edge_cell_cover
#print axioms RootedKP.AKLT.Polymer.core_trace_trimmed
#print axioms RootedKP.AKLT.four_root_count_relaxed
#print axioms RootedKP.AKLT.relaxed_long_slope
#print axioms RootedKP.AKLT.uniformKP_of_prefix_catalog
#print axioms RootedKP.AKLT.scalar_bound_of_prefix_catalog
#print axioms RootedKP.AKLT.uniform_rooted_summability_of_prefix_catalog
#check RootedKP.Heaps.rooted_heap_KP_of_criterion
#check RootedKP.AKLT.uniform_rooted_summability_of_kp_and_root_mass
#check RootedKP.AKLT.scalarSum_le_of_uniform_kp
#check RootedKP.AKLT.scalar_bound_of_prefix_catalog_and_four
#check RootedKP.AKLT.scalar_bound_of_prefix_catalog

-- Closed finite certificates and final model-specific conclusions.
#print axioms RootedKP.PackedSupports.vertexCode_injective
#print axioms RootedKP.PackedSupports.overlap_hitsRoot
#print axioms RootedKP.CachedPaths.hitCount_gather
#print axioms RootedKP.CachedPaths.catalogCount_eq_allMasks
#print axioms RootedKP.CachedPaths.codeHitCount_eq
#print axioms RootedKP.CachedPaths.codeCountByStarts_eq
#print axioms RootedKP.CachedPaths.coversFour
#print axioms RootedKP.CachedPaths.coversFive
#print axioms RootedKP.CachedPaths.coversSix
#print axioms RootedKP.CachedPaths.coversLoop
#print axioms RootedKP.CachedPaths.verifiedRowsFour
#print axioms RootedKP.CachedPaths.verifiedRowsFive
#print axioms RootedKP.CachedPaths.verifiedRowsSix
#print axioms RootedKP.CachedPaths.verifiedRowsLoop
#print axioms RootedKP.AKLT.shortPrefixCatalogBounds
#print axioms RootedKP.AKLT.uniformKP_certified
#print axioms RootedKP.AKLT.edge_root_mass_certified
#print axioms RootedKP.AKLT.uniform_root_mass_certified
#print axioms RootedKP.AKLT.scalar_bound_certified
#print axioms RootedKP.AKLT.rooted_summability_certified
#check RootedKP.AKLT.shortPrefixCatalogBounds
#check RootedKP.AKLT.uniformKP_certified
#check RootedKP.AKLT.edge_root_mass_certified
#check RootedKP.AKLT.scalar_bound_certified
#check RootedKP.AKLT.rooted_summability_certified
#print RootedKP.AKLT.UniformKPCondition
#print RootedKP.AKLT.UniformRootedSummability
