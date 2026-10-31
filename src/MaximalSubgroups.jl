"""
    MaximalSubgroups

A package for computing anisotropic root systems (φₐ) of quasimaximal
subsystems, together with the diagram-automorphism permutations and the
permutation-to-matrix maps used in the analysis of maximal subgroups.
"""
module MaximalSubgroups
__precompile__(false)

using Oscar
using Graphs

# ---- modules in dependency order ----
include("vector_space_helpers.jl")
include("root_system_helpers.jl")
include("validate_input_types.jl")
include("descriptor_resolver.jl")
include("permutation_matrix.jl")
include("anisotropic_system.jl")

# ---- exports ----
export anisotropic_system
export diagram_automorphism
export permutation_to_matrix
export simple_root_embedding

end # module