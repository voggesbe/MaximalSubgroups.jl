# ---------------------------------------------------------------------------
# test/support/helpers.jl
#
# Pure helper functions shared across the test suite. This file is *included*
# from `runtests.jl`, so it must ONLY define things. It must never execute a
# test assertion or call library code at load time -- otherwise the error would
# surface when the suite is imported, not when it is run, and would be reported
# as a hard LoadError instead of a normal failing `@test`.
# ---------------------------------------------------------------------------

"""
    _components(g) -> Vector{Tuple{Symbol,Int}}

`p_a` reports the resulting subsystem as `root_system_G`: a list of
`[(type, rank), multiplicity]` pairings. This helper flattens that structure
into the multiset of `(type, rank)` tuples (ignoring per-component
multiplicities) so a test can simply write `@test (:B, 6) in _components(g)`.
"""
function _components(g)
    found = Tuple{Symbol,Int}[]
    for pairing in g
        # each element of g is `[(type, rank), count]`
        push!(found, Tuple{Symbol,Int}(pairing[1]))
    end
    return found
end